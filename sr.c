#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"


#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet
                          MUST BE SET TO 6 when submitting assignment */
#define SEQSPACE 12     /* the min sequence space for SR = 2N */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet) /*sender create checksum for pkt*/
{
  int checksum = 0;
  int i;
  /*change check method with 16 bit checksum*/
  checksum ^= packet.seqnum; /*XOR checksum with seqnum*/
  checksum ^= packet.acknum; /*also do with acknum*/
  for (i = 0; i < 20; ++i) {
      checksum ^= (packet.payload[i] << ((i % 4) * 8)); /*also do with payload data*/
  }

  return checksum;
}

/*if the current packet checksum is not same as the original, it is corrupted*/
bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE];  /* array for storing packets waiting for ACK */
static int windowfirst, windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */
static bool acked[WINDOWSIZE];         /* array for ACK to check which pkt already ACKed */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked wait ACK */
  if ( windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;

    /*check sum*/
    for ( i=0; i<20 ; i++ )
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* put pkt in buffer, update */
    windowlast = (windowlast + 1) % WINDOWSIZE;
    buffer[windowlast] = sendpkt;
    windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3 (A, sendpkt);

    /* start timer if first packet in window */
    if (windowcount == 1)
      starttimer(A,RTT);

    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
  }
  /* if blocked,  window is full */
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{

  /*ACK of gbn is cumulative (ACK n), but ACK for sr is independent, each pkt has own ACK*/
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);

    /*check received ACK corrupted & got before or not */
    if (!acked[packet.acknum]) {
      if (TRACE > 0)
        printf("----A: ACK %d is not a duplicate\n",packet.acknum);
      new_ACKs++;
      acked[packet.acknum] = true;

      /*Attempt to slide the window only if the received ACK is the leftmost (earliest) packet in the window.*/
      if (packet.acknum == buffer[windowfirst].seqnum) {
        while (windowcount > 0) {
          if (!acked[buffer[windowfirst].seqnum]) break;
          windowfirst = (windowfirst + 1) % WINDOWSIZE;
          windowcount--;
          }

	    /* stop or start if still have pkt not ACKed */
      stoptimer(A);
      if (windowcount > 0)
        starttimer(A, RTT);

    }
  }
      else if (TRACE > 0)
      printf ("----A: duplicate ACK received, do nothing!\n");
  }
  else if (TRACE > 0)
      printf ("----A: corrupted ACK is received, do nothing!\n");
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
    if (TRACE > 0)
      printf("----A: time out,resend packets!\n");

    if (TRACE > 0)
      printf ("---A: resending packet %d\n", (buffer[windowfirst]).seqnum);
    
    /*only resend if the leftmost (earliest) packet in the window not ACKed.*/
    tolayer3(A,buffer[windowfirst]); 
    packets_resent++;

    /* same above*/
    if (windowcount > 0) {
      starttimer(A, RTT);
    }
  
}



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.
		     new packets are placed in winlast + 1
		     so initially this is set to -1
		   */
  windowcount = 0;
}



/********* Receiver (B)  variables and procedures ************/

static int expectedseqnum; /* the sequence number expected next by the receiver */
static struct pkt pkt_r[SEQSPACE]; /* cached array for storing packets received out of order */
static bool pkt_r_acked[SEQSPACE]; /* to save ACK is recevied or not */


/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;

  /* if not corrupted and received packet is in order */
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
    packets_received++;

    /*Cache unreceived packets in the receive window*/
    if (!pkt_r_acked[packet.seqnum]) {
      pkt_r[packet.seqnum] = packet;
      pkt_r_acked[packet.seqnum] = true;
    }

    /* send an ACK for the received packet */
    sendpkt.acknum = packet.seqnum;
    sendpkt.seqnum = 0;
    for (i = 0; i < 20; i++) sendpkt.payload[i] = '.';
    sendpkt.checksum = ComputeChecksum(sendpkt);
    tolayer3(B, sendpkt);

    /* Check the cache for packages that can be delivered in order */
    while (pkt_r_acked[expectedseqnum]) 
    {
      tolayer5(B, pkt_r[expectedseqnum].payload);
      pkt_r_acked[expectedseqnum] = false;
      /* update state variables */
      expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
    }
  }
  else {
    /* Send ACK even if you receive a damaged package.*/
    if (TRACE > 0)
      printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");

    /* create packet */
    sendpkt.acknum = packet.seqnum;
    sendpkt.seqnum = 0;

    /* we don't have any data to send.  fill payload with 0's */
    for ( i=0; i<20 ; i++ )
      sendpkt.payload[i] = '.';

    /* computer checksum */
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* send out packet */
    tolayer3 (B, sendpkt);
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  expectedseqnum = 0;
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}
