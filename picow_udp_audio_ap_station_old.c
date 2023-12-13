/**
 * Copyright (c) 2022 Andrew McDonnell
 * SPDX-License-Identifier: BSD-3-Clause
 */
/*
 * UDP sned/receive Adapted from:
 ** Copyright (c) 2016 Stephan Linz <linz@li-pro.net>, Li-Pro.Net
 * All rights reserved.
 *
 * Based on examples provided by
 * Iwan Budi Kusnanto <ibk@labhijau.net> (https://gist.github.com/iwanbk/1399729)
 * Juri Haberland <juri@sapienti-sat.org> (https://lists.gnu.org/archive/html/lwip-users/2007-06/msg00078.html)
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * This file is part of and a contribution to the lwIP TCP/IP stack.
 * Credits go to Adam Dunkels (and the current maintainers) of this software.
 * Stephan Linz rewrote this file to get a basic echo example.
 * =============================================================
 * UDP send/recv code is from :
 * Pico examples  
 * https://github.com/raspberrypi/pico-examples/tree/master/pico_w/wifi/udp_beacon
 * lwip contrib apps 
 * https://github.com/lwip-tcpip/lwip/tree/master/contrib/apps
 * UDP send/recv on Windows is from:
 * Microsoft 
 * https://apps.microsoft.com/store/detail/udp-senderreciever/9NBLGGH52BT0?hl=en-us&gl=us
 * a bare-bones packet whacker
 * =============================================================
 * Threads:
 * Core0:
 * -- udp send -- core1 generates DDS audio in ISR
 * -- udp recv -- core1 plays audio thru SPI DAC in ISR
 * -- LWIP receive callback routine
 * Core1:
 * -- blink cyw43 LED
 * -- serial for debug, set the mode to 'send, recv' turn on and set freq of DDS
 * -- audio synthesis/playback
 * 
 * figure out addresses
 * -- pico discovery:
 *      in send mode: broadcast sender's IP address. format IP xxx.xxx.xxx.xxx
 *      pico in echo mode: sees braodcast and sends it's IP address back to sender's IP addr
 */

#include <string.h>
#include <stdlib.h>
#include <pico/multicore.h>
#include "hardware/sync.h"
#include "hardware/gpio.h"
#include "hardware/timer.h"
#include "hardware/spi.h"
#include "hardware/uart.h"
#include "stdio.h"
#include "math.h"

#include "pico/stdlib.h"
#include "pico/cyw43_arch.h"

#include "lwip/pbuf.h"
#include "lwip/udp.h"
#include "lwip/opt.h"
#include "lwip/debug.h"
#include "lwip/stats.h"
#include "lwip/dns.h"
#include "lwip/netif.h"
#include "lwip/tcp.h"
#include "dhcpserver/dhcpserver.h"
#include "pico/stdlib.h"
#include "pico/multicore.h"

// Include hardware libraries
#include "hardware/pwm.h"
#include "hardware/dma.h"
#include "hardware/irq.h"
#include "hardware/adc.h"
#include "hardware/pio.h"
#include "hardware/i2c.h"

// Include custom libraries
#include "vga_graphics.h"
#include "mpu6050.h"

//++++++++++++++++++++++++
//GAME SETUP:
//++++++++++++++++++++++++
fix15 acceleration[3], gyro[3];

// character array
char screentext[40];

// draw speed
int threshold = 10;

// Some macros for max/min/abs
#define min(a, b) ((a < b) ? a : b)
#define max(a, b) ((a < b) ? b : a)
#define abs(a) ((a > 0) ? a : -a)

// semaphore
static struct pt_sem vga_semaphore;
#define PI 3.14159265

// IMU angle estimation
fix15 accel_angle;
fix15 gyro_angle_delta;
fix15 complementary_angle = 0;
fix15 filtered_complementary;
fix15 filtered_ax;
fix15 filtered_ay;

// Game variables
#define PADDLE1_X 40
#define PADDLE2_X 590
#define PADDLE_LENGTH 60
#define VGA_BOTTOM 480
#define VGA_RIGHT 640
#define BALL_RADIUS 5

fix15 ball_x = int2fix15(320);
fix15 ball_y = int2fix15(240);
float ball_angle = PI*2/3;
fix15 ball_vx = float2fix15(0.1);
fix15 ball_vy = float2fix15(0.3);

fix15 paddle1_y = int2fix15(240);
fix15 paddle1_vy = 0;
fix15 paddle2_y = int2fix15(240);
fix15 paddle2_vy = float2fix15(0.5);
int player1 = 0;
int player2 =0;
bool play_game = true;

//++++++++++++++++++++++++
//WIRELESS SETUP:
//++++++++++++++++++++++++
// ======================================
// set automatic setup on if defined
// --pairs the two devices then
// --puts the receiver in 'play' mode
//--Only commands available are 'play' and 'stop'
//    on transmitter side
#define auto_setup

// udp constants
#define UDP_PORT 4444
#define UDP_MSG_LEN_MAX 1400 // max length without fragments
// following is used only if auto_setup is not defined
#define UDP_TARGET_BROADCAST "255.255.255.255"
//#define UDP_INTERVAL_MS 10 // not used
// should resolve to a actual addr after pairing
char udp_target_pico[20] =  "255.255.255.255" ;

// choose appropriate packet length
enum packet_lengths {command, ack, data} packet_length = command ;

// =======================================
// necessary to connect to wireless
// on the picow access point
#define WIFI_SSID "picow_test"
#define WIFI_PASSWORD "password"
// predeine the station address
#define STATION_ADDR "192.168.4.10"

// =======================================
// protothreads and thread communication
#include "pt_cornell_rp2040_v1_1_2.h"
char recv_data[UDP_MSG_LEN_MAX];
char send_data[UDP_MSG_LEN_MAX];

// payload to led blink
// or send to remote system
int blink_time, remote_blink_time ;
// interthread communicaition
// signal threads for sned/recv data
struct pt_sem new_udp_recv_s, new_udp_send_s ;
// mode: send/echo
// send mode is in chage here, defined by seril input
// both units default to echo
#define echo 0
#define send 1
int mode = echo ;
int play = false ;
// did the addresses get set up?
int paired = false ;
// data to send over WIFI
#define max_data_size  512 
int data_size = 500; // 512
// double buffer the sent data to avoid skips
short data_buffer[max_data_size] ; 
// buffer_number is 0 or 1
int tx_buffer_index, rx_buffer_index ;

// the following MUST be less than or equal to:
// UDP_MSG_LEN_MAX
// but for efficiency, not much smaller
#define send_data_size data_size*sizeof(short)
//record time for packet speed determination
uint64_t time1;

// ========================================
// === spi setup 
// =======================================
//SPI configurations
#define PIN_CS   5
#define PIN_SCK  6
#define PIN_MOSI 7
#define SPI_PORT spi0

// constant to tell SPI DAC what to do
// prepend to each 12-bit sample
#define DAC_config_chan_A 0b0011000000000000
// B-channel, 1x, active
#define DAC_config_chan_B 0b1011000000000000
uint16_t DAC_data ; 

// ================================================
// DDS variables 
#define sin_table_len 256
short sine_table[sin_table_len] ;
short sine_table_out ;
// the desired frequency output
float Fout ;
// 1/Fs in microseconds for ISR
// 40000 works
// 40000x8x2 = 0.64 Mbits/sec
// 100000 , but the send side complains of 'unexpected packet'
// 100000x8x2 = 1.6 Mbits/sec
// 200000, glitchy waveform -- call this a FAIL
// 150000, glitchy waveform -- call this a FAIL
// 120000, glitchy waveform -- call this a FAIL
// 80000 works, but the send side complains of 'unexpected packet'
// 80000x8x2 = 1.28 Mbits/sec
// 62500 works, but the send side complains of 'unexpected packet'
// 1 Mbit/sec
// 50000 works 800 Kbits/sec
#define Fs 40000 // per second
volatile int alarm_period = 1000000 ;
volatile unsigned int main_inc = 400 * 4294967296 / Fs ; //2^32
volatile unsigned int main_accum ;
// send uses this to save in buffer, recv uses it for DAC
short sin_data ;

// ==========================================
// === set up timer ISR  used in this pgm
// ==========================================
// === timer alarm ========================
// !! modifiying alarm15 ball zero trashes the cpu 
//        and causes LED  4 long - 4 short
// !! DO NOT USE alarm 0
// This low-level setup is ocnsiderably faster to execute
// than the hogh-level callback

#define ALARM_NUM 2 //1
#define ALARM_IRQ TIMER_IRQ_2 //1
// ISR interval will be 10 uSec
//
// the actual ISR
void compute_sample(void);
//
static void alarm_irq(void) {
    // mark ISR entry
    //gpio_put(2,1);
    // Clear the alarm irq
    hw_clear_bits(&timer_hw->intr, 1u << ALARM_NUM);
    // arm the next interrupt
    // Write the lower 32 bits of the target time to the alarm to arm it
    timer_hw->alarm[ALARM_NUM] = timer_hw->timerawl + alarm_period ;
    //
    compute_sample();
    // mark ISR exit
    //gpio_put(2,0);
}

// set up the timer alarm ISR
static void alarm_in_us(uint32_t delay_us) {
    // Enable the interrupt for our alarm (the timer outputs 4 alarm irqs)
    hw_set_bits(&timer_hw->inte, 1u << ALARM_NUM);
    // Set irq handler for alarm irq
    irq_set_exclusive_handler(ALARM_IRQ, alarm_irq);
    // Enable the alarm irq
    irq_set_enabled(ALARM_IRQ, true);
    // Enable interrupt in block and at processor
    // Alarm is only 32 bits 
    uint64_t target = timer_hw->timerawl + delay_us;
    // Write the lower 32 bits of the target time to the alarm which
    // will arm it
    timer_hw->alarm[ALARM_NUM] = (uint32_t) target;   
}
// ==================================================
// === dsp ISR -- RUNNING on core 1
// ==================================================
// 
int count_isr ;
void compute_sample(void)
{
    count_isr++ ;
    if ((mode==send) && play){

      printf("sending");
      short valid_game = 1;
      short ball_xx = (short)(fix2int15(ball_x));
      short ball_yy = (short)(fix2int15(ball_y));
      short player1_xx = (short)(fix2int15(ball_x));
      short player1_yy = (short)(fix2int15(ball_y));
      short player1_score = (short)(player1);
      short player2_score = (short)(player2);
      
      data_buffer[0] = valid_game;
      data_buffer[1] = ball_xx;
      data_buffer[2] = ball_yy;
      data_buffer[3] = player1_xx;
      data_buffer[4] = player1_yy;
      data_buffer[5] = (short)count_isr + 1000; //player1_score;
      data_buffer[6] = player2_score;
      data_buffer[7] = (short)(play_game);

      printf("%hd", player1_score);
      // if full, signal send and copy buffer
      if (true){
        memcpy(send_data, data_buffer, send_data_size) ;
        tx_buffer_index = 0;
        packet_length = data ;
        PT_SEM_SIGNAL(pt, &new_udp_send_s) ;
      }

      printf("receving");
      short currentShort = *((short*)recv_data);
      printf("%hd",currentShort);


    }

    else if ((mode==echo) && play ){

      printf("sending");
      data_buffer[0] = count_isr + 200;
      printf("%hd", (count_isr + 200));
      // if full, signal send and copy buffer
      if (true){
        memcpy(send_data, data_buffer, send_data_size) ;
        tx_buffer_index = 0;
        packet_length = data ;
        PT_SEM_SIGNAL(pt, &new_udp_send_s) ;
      }


      printf("receving");
      short currentShort = ((short*)(recv_data))[5];
      printf("%hd",currentShort);
    }
} // isr sample routine

//
//==================================================
// UDP async receive callback setup
// NOTE that udpecho_raw_recv is triggered by a signal
// directly from the LWIP package -- not from your code
// this callback juswt copies out the packet string
// and sets a "new data" semaphore
// This runs in an ISR -- KEEP IT SHORT!!!

#if LWIP_UDP

static struct udp_pcb *udpecho_raw_pcb;
//struct pbuf *p ;

//static void
void __not_in_flash_func(udpecho_raw_recv)(void *arg, struct udp_pcb *upcb, struct pbuf *p,
                 const ip_addr_t *addr, u16_t port)
{
  LWIP_UNUSED_ARG(arg);
  //gpio_put(3,1);
  if (p != NULL) {
    //printf("p payload in call back: = %s\n", p->payload);
    memcpy(recv_data, p->payload, UDP_MSG_LEN_MAX);
    /* free the pbuf */ 
    pbuf_free(p);
    // can signal from an ISR -- BUT NEVER wait in an ISR
    // dont waste time if actaullly playing
    if(!(play && (mode==echo)))
        PT_SEM_SIGNAL(pt, &new_udp_recv_s) ;
  }
  else printf("NULL pt in callback");
  //gpio_put(3,0);
}

// ===================================
// Define the recv callback 
void 
udpecho_raw_init(void)
{
  struct pbuf *p ; // OMVED
  udpecho_raw_pcb = udp_new_ip_type(IPADDR_TYPE_ANY);
  p = pbuf_alloc(PBUF_TRANSPORT, UDP_MSG_LEN_MAX+1, PBUF_POOL);

  if (udpecho_raw_pcb != NULL) {
    err_t err;
    // netif_ip4_addr returns the picow ip address
    err = udp_bind(udpecho_raw_pcb, netif_ip4_addr(netif_list), UDP_PORT); //DHCP addr

    if (err == ERR_OK) {
      udp_recv(udpecho_raw_pcb, udpecho_raw_recv, NULL);
      //printf("Set up recv callback\n");
    } else {
      printf("bind error");
    }
  } else {
    printf("udpecho_raw_pcb error");
  }
}

#endif /* LWIP_UDP */
// end recv setup

// =======================================
// UDP send thead
// sends data when signalled
// =======================================
static ip_addr_t addr;
static PT_THREAD (protothread_udp_send(struct pt *pt))
 { PT_BEGIN(pt);
    static struct udp_pcb* pcb;
    pcb = udp_new();
    pcb->remote_port = UDP_PORT ;
    pcb->local_port = UDP_PORT ;

    static int counter = 0;
    
    while (true) {
        
        // stall until there is actually something to send
        PT_SEM_WAIT(pt, &new_udp_send_s) ;

        // in paired mode, the two picos talk just to each other
        // before pairing, the echo unit talks to the laptop
        if(mode == echo) {
          if(paired == true){
                ipaddr_aton(udp_target_pico, &addr);
            }
            else{
                ipaddr_aton(udp_target_pico, &addr);
            }         
        }
        // broadcast mode makes sure that another pico sees the packet
        // to sent an address and for testing
        else if(mode == send) {
            if(paired == true){
                ipaddr_aton(udp_target_pico, &addr);
            }
            else{
                ipaddr_aton(UDP_TARGET_BROADCAST, &addr);
            }
        }

        // get the length specified by another thread
        static int udp_send_length ;
        switch (packet_length){
          case command:
            udp_send_length = 32 ;
            break;
          case data:
            udp_send_length = send_data_size ;
            break;
          case ack:
            udp_send_length = 5 ;
            break;
        }

       // actual data-send
        struct pbuf *p = pbuf_alloc(PBUF_TRANSPORT, udp_send_length+1, PBUF_RAM);
        char *req = (char *)p->payload;
        memset(req, 0, udp_send_length+1);//
         memcpy(req, send_data, udp_send_length) ;
        //
        //cyw43_arch_lwip_begin();
        err_t er = udp_sendto(pcb, p, &addr, UDP_PORT); //port
        //cyw43_arch_lwip_end();
       
        pbuf_free(p);
        if (er != ERR_OK) {
            printf("Failed to send UDP packet! error=%d", er);
        } else {
           // printf("Sent packet %d\n", counter);
            counter++;
        }
    }
    PT_END(pt);
}

// ==================================================
// udp recv processing
// ==================================================
static PT_THREAD (protothread_udp_recv(struct pt *pt))
{
    PT_BEGIN(pt);
        static char  arg1[32], arg2[32], arg3[32] , arg4[32]  ;
        static char* token ;
    
     // data structure for interval timer
     //PT_INTERVAL_INIT() ;

      while(1) {
        // wait for new packet
        // signalled by LWIP receive ISR
        PT_SEM_WAIT(pt, &new_udp_recv_s) ;       
        
        // parse command         
          token = strtok(recv_data, "  ");
          strcpy(arg1, token) ;
          token = strtok(NULL, "  ");
          strcpy(arg2, token) ;

          // is this a pairing packet (starts with IP)
          // if so, parse address 
          // process packet to get time
          if((strcmp(arg1,"IP")==0) && !play){
            if(mode == echo){
                // if I'm the echo unit, grab the address of the other pico
                // for the send thread to use
                strcpy(udp_target_pico, arg2) ;
                //        
                paired = true ;
                // then send back echo-unit address to send-pico
                memset(send_data, 0, UDP_MSG_LEN_MAX) ;
                sprintf(send_data,"IP %s" ,ip4addr_ntoa(netif_ip4_addr(netif_list))) ;
                packet_length = command ;
                // local effects
                printf("sent back IP %s\n\r", ip4addr_ntoa(netif_ip4_addr(netif_list)));
                blink_time = 500 ;
                // tell send threead 
                PT_SEM_SIGNAL(pt, &new_udp_send_s) ;
                PT_YIELD(pt);
            }
            else{
              // if I'm the send unit, then just save for future transmit
              strcpy(udp_target_pico, arg2) ;
            }
          } // end  if(strcmp(arg1,"IP")==0)

          // is it ack packet ?
          else if((strcmp(arg1,"ack")==0) && !play){
            if(mode == send){
                // print a long-long 64 bit int
                printf("%lld usec ack\n\r", PT_GET_TIME_usec()-time1);
            }
            if((mode == echo ) && !play){
                memset(send_data, 0, UDP_MSG_LEN_MAX) ;
                sprintf(send_data,"ack" ) ;   
                packet_length = ack ;     
                // tell send threead 
                PT_SEM_SIGNAL(pt, &new_udp_send_s) ;
                PT_YIELD(pt);
            }
          }

        // NEVER exit while
      } // END WHILE(1)
    PT_END(pt);
} // recv thread

// ==================================================
// toggle cyw43 LED  
// this is really just a test of multitasking
// compatability with LWIP 
// but also reads out pair status
// ==================================================
static PT_THREAD (protothread_toggle_cyw43(struct pt *pt))
{
    PT_BEGIN(pt);
    static bool LED_state = false ;
    //
     // data structure for interval timer
     PT_INTERVAL_INIT() ;
     // set some default blink time
     blink_time = 100 ;
     // echo the default time to udp connection
     // PT_SEM_SIGNAL(pt, &new_udp_send_s) ;

      while(1) {
        // force a context switch of there is data to send
        if(&new_udp_send_s.count) PT_YIELD(pt);
        //
        LED_state = !LED_state ;
        
        cyw43_arch_lwip_begin();
        // the onboard LED is attached to the wifi module
        cyw43_arch_gpio_put(CYW43_WL_GPIO_LED_PIN, LED_state);
        cyw43_arch_lwip_end();
        // blink time is modifed by the udp recv thread
        PT_YIELD_INTERVAL(blink_time*1000) ;
        //
        // NEVER exit while
      } // END WHILE(1)
    PT_END(pt);
} // blink thread

// =================================================
// command thread
// =================================================
static PT_THREAD (protothread_serial(struct pt *pt))
{
    PT_BEGIN(pt);
        static char cmd[16], arg1[16], arg2[16] ;
        static char* token ;
      //
      if(mode==send)
        printf("Type 'help' for commands\n\r") ;

      while(1) {
        // the yield time is not strictly necessary for protothreads
        // but gives a little slack for the async processes
        // so that the output is in the correct order (most of the time)
        PT_YIELD_usec(100000);

        if(mode==send){
          // print prompt
          sprintf(pt_serial_out_buffer, "cmd> ");
        }
        else{
          sprintf(pt_serial_out_buffer, "no cmd in recv mode ");
        }
          // spawn a thread to do the non-blocking write
          serial_write ;
        
          // spawn a thread to do the non-blocking serial read
          serial_read ;
          // tokenize
          token = strtok(pt_serial_in_buffer, "  ");
          strcpy(cmd, token) ;
          token = strtok(NULL, "  ");
          strcpy(arg1, token) ;
          token = strtok(NULL, "  ");
          strcpy(arg2, token) ;
          //token = strtok(NULL, "  ");
          //strcpy(arg3, token) ;
          //token = strtok(NULL, "  ");
          //strcpy(arg4, token) ;
          //token = strtok(NULL, "  ");
          //strcpy(arg5, token) ;
          //token = strtok(NULL, "  ");
          //strcpy(arg6, token) ;
        

        // parse by command
        if(strcmp(cmd,"help")==0){
            // commands 
            //printf("set mode [send, recv]\n\r");  
            printf("play frequency\n\r"); 
            printf("stop \n\r");  
            printf("pair \n\r");
            printf("ack \n\r");
            //printf("data array_size \n\r");
            // 
            // need start data and end data commands
        }
        
        /* this is now done in MAIN before network setup
        // set the unit mode
        else if(strcmp(cmd,"set")==0){
            if(strcmp(arg1,"recv")==0) {
                mode = echo ;
            }
            else if(strcmp(arg1,"send")==0) mode = send ;
            else printf("bad mode");
                //printf("%d\n", mode);
        }
        */

        // identify other pico on the same subnet
        // not needed if autp_setup defined
        else if(strcmp(cmd,"pair")==0){
            if(mode == send) {
                // broadcast sender's IP addr
                memset(send_data, 0, UDP_MSG_LEN_MAX) ;
                sprintf(send_data,"IP %s" ,ip4addr_ntoa(netif_ip4_addr(netif_list))) ;
                packet_length = command ;
                PT_SEM_SIGNAL(pt, &new_udp_send_s) ;
                // diagnostics:
                printf("send IP %s\n" ,ip4addr_ntoa(netif_ip4_addr(netif_list))) ;
                // boradcast until paired
                printf("sendto IP %s\n" , udp_target_pico) ;
                // probably shoulld be some error checking here               
                paired = true ;
            } 
            else printf("No pairing in recv mode -- set send\n");          
        }

        // send ack packet
        else if(strcmp(cmd,"ack")==0){
            if(mode == send) {
                memset(send_data, 0, UDP_MSG_LEN_MAX) ;
                sprintf(send_data,"ack" ) ;
                packet_length = ack ;
                time1 = PT_GET_TIME_usec();
                PT_SEM_SIGNAL(pt, &new_udp_send_s) ;
                // yield so that send thread gets faster access
                PT_YIELD(pt);
            } 
            else printf("No ack in recv mode -- set send\n");          
        }

        // send DDS to the other pico in the alarm ISR
        else if(strcmp(cmd,"play")==0){
            packet_length = data ;
            play = true ;
            tx_buffer_index = 0 ;
            rx_buffer_index = 0 ;
            if(mode == send){ 
              sscanf(arg1, "%f", &Fout);
              main_inc = (unsigned int)(Fout * 4294967296 / Fs);
              main_accum = 0 ;
            }
        }

        else if(strcmp(cmd,"stop")==0){
            main_inc = 0 ;
            main_accum = 0 ;
            PT_YIELD_usec(50000);
            play = false ;
        }

        // no valid command
        else printf("Huh? Type help. \n\r") ;

        // NEVER exit while
      } // END WHILE(1)

  PT_END(pt);
} // serial thread



typedef struct TCP_SERVER_T_ {
    struct tcp_pcb *server_pcb;
    bool complete;
    ip_addr_t gw;
    async_context_t *context;
} TCP_SERVER_T;
static PT_THREAD(protothread_paddle1(struct pt *pt))
{
  PT_BEGIN(pt);
  while (true)
  {
    // wait for 0.1 sec
    PT_YIELD_usec(100);
    if (play_game){
      // Read the IMU
      // NOTE! This is in 15.16 fixed point. Accel in g's, gyro in deg/s
      // If you want these values in floating point, call fix2float15() on
      // the raw measurements.
      mpu6050_read_raw(acceleration, gyro);

      // Accelerometer angle (degrees - 15.16 fixed point)
      // Only ONE of the two lines below will be used, depending whether or not a small angle approximation is appropriate
      filtered_ax = filtered_ax + ((acceleration[1] - filtered_ax) >> 4);
      filtered_ay = filtered_ay + ((acceleration[2] - filtered_ay) >> 4);

      // NO SMALL ANGLE APPROXIMATION
      accel_angle = multfix15(float2fix15(atan2(fix2float15(-filtered_ay), fix2float15(filtered_ax)) + PI), oneeightyoverpi);

      // Gyro angle delta (measurement times timestep) (15.16 fixed point)
      gyro_angle_delta = multfix15(gyro[0], zeropt001);

      // Complementary angle (degrees - 15.16 fixed point)
      complementary_angle = multfix15(complementary_angle + gyro_angle_delta, zeropt999) + multfix15(accel_angle, zeropt001);
      filtered_complementary = filtered_complementary + ((complementary_angle - filtered_complementary) >> 4);

      // When the arm swings past 0 degrees, set it to zero
      if (filtered_complementary > int2fix15(180))
      {
        filtered_complementary = int2fix15(180);
      }
      if (filtered_complementary < 0)
      {
        filtered_complementary = 0;
      }

      // Changing y position of paddle 1
      paddle1_vy = 0 - multfix15((filtered_complementary - int2fix15(90)), float2fix15(0.005));

      if (paddle1_vy > float2fix15(0.9))
      {
        paddle1_vy = float2fix15(0.9);
      }
      if (paddle1_vy < float2fix15(-0.9))
      {
        paddle1_vy = float2fix15(-0.9);
      }

      // erase paddle
      fillRect(PADDLE1_X, fix2int15(paddle1_y), 10, PADDLE_LENGTH, BLACK);

      if (paddle1_y + paddle1_vy <= 0)
      {
        paddle1_y = 0;
      }
      else if (paddle1_y + paddle1_vy + int2fix15(PADDLE_LENGTH) >= int2fix15(VGA_BOTTOM))
      {
        paddle1_y = int2fix15(VGA_BOTTOM - PADDLE_LENGTH);
      }
      else
      {
        paddle1_y += paddle1_vy;
      }

      // draw paddle
      fillRect(PADDLE1_X, fix2int15(paddle1_y), 10, PADDLE_LENGTH, WHITE);
    }
  }
  PT_END(pt);
}

// Thread that draws to paddle2
static PT_THREAD(protothread_paddle2(struct pt *pt))
{
  // Indicate start of thread
  PT_BEGIN(pt);

  while (true)
  {
    PT_YIELD_usec(100);
    if (play_game){
      // erase paddle
      fillRect(PADDLE2_X, fix2int15(paddle2_y), 10, PADDLE_LENGTH, BLACK);
      // Changing y position of paddle 2
      if (paddle2_y <= 0)
      {
        paddle2_vy = float2fix15(0.09);
      }
      if (paddle2_y + int2fix15(PADDLE_LENGTH) >= int2fix15(VGA_BOTTOM))
      {
        paddle2_vy = float2fix15(-0.09);
      }
      paddle2_y += paddle2_vy;

      // draw paddle
      fillRect(PADDLE2_X, fix2int15(paddle2_y), 10, PADDLE_LENGTH, WHITE);
    }
  }

  // Indicate end of thread
  PT_END(pt);
}

// Thread that draws to the ball
static PT_THREAD(protothread_ball1(struct pt *pt))
{
  // Indicate start of thread
  PT_BEGIN(pt);

  while (1)
  {
    // wait for 0.1 sec
    PT_YIELD_usec(100);
    if (play_game){
    // Changing position of ball
      if (ball_x >= int2fix15(VGA_RIGHT))
      {
        // erase ball
        fillCircle(fix2int15(ball_x), fix2int15(ball_y), BALL_RADIUS, BLACK);
        ball_x = int2fix15(VGA_RIGHT / 2);
        ball_y = int2fix15(VGA_BOTTOM / 2);
        ball_vx = 0 - ball_vx;
        player1 += 1;
      }
      if ( ball_x <= 0)
      {
        // erase ball
        fillCircle(fix2int15(ball_x), fix2int15(ball_y), BALL_RADIUS, BLACK);
        ball_x = int2fix15(VGA_RIGHT / 2);
        ball_y = int2fix15(VGA_BOTTOM / 2);
        ball_vx = 0 - ball_vx;
        player2 += 1;
      }
   
      if (ball_y >= int2fix15(VGA_BOTTOM) || ball_y <= 0)
      {
        ball_vy = 0 - ball_vy;
      }

      if (ball_x > int2fix15(PADDLE1_X + 12) && ball_x < int2fix15(PADDLE1_X + 18))
      {
        if (ball_y > paddle1_y && ball_y < paddle1_y + int2fix15(PADDLE_LENGTH))
        {
          ball_vx = float2fix15(0.1);
        }
      }

      if (ball_x < int2fix15(PADDLE2_X + 2) && ball_x > int2fix15(PADDLE2_X - 8))
      {
        if (ball_y > paddle2_y && ball_y < paddle2_y + int2fix15(PADDLE_LENGTH))
        {
          ball_vx = float2fix15(-0.1);
        }
      }
      //erase ball
      fillCircle(fix2int15(ball_x), fix2int15(ball_y), BALL_RADIUS, BLACK);

      ball_x += ball_vx;
      ball_y += ball_vy;

      // draw ball
      fillCircle(fix2int15(ball_x), fix2int15(ball_y), BALL_RADIUS, WHITE);
    }
  }

  // Indicate end of thread
  PT_END(pt);
}

char str[10];
static PT_THREAD(protothread_score(struct pt *pt))
{
  PT_BEGIN(pt);
  while (1){
    setCursor(100, 15);
    setTextSize(2);
    sprintf(str, "Player 1 = %d  ", player1);
    setTextColor2(WHITE, BLACK);
    writeString(str);
   
    setCursor(400, 15);
    sprintf(str, "Player 2 = %d  ", player2);
    setTextColor2(WHITE, BLACK);
    writeString(str);

    if (player1 == 10){
      setCursor(200, 240);
      sprintf(str, "Player 1 wins!");
      setTextColor2(WHITE, BLACK);
      writeString(str);

      play_game = false;
    }

    if (player2 == 10){
      setCursor(200, 240);
      sprintf(str, "Player 2 wins!");
      setTextColor2(WHITE, BLACK);
      writeString(str);
      play_game = false;
    }

    PT_YIELD_usec(100000);
  }
  PT_END(pt);
}
// ========================================
// === core 1 main -- started in main below
// ========================================
void core1_main(){ 
  //
  //  === add threads  ====================
  // for core 1
   // ISR to handle analog
    alarm_in_us(alarm_period);
    //
    // put slow threads on core 1
    pt_add_thread(protothread_toggle_cyw43) ;
    pt_add_thread(protothread_serial) ;
    pt_add_thread(protothread_paddle2);
    //
    pt_schedule_start ;

  //
  // === initalize the scheduler ==========
  //pt_schedule_start ;
  // NEVER exits
  // ======================================
}
// ====================================================
int main() {
  // =======================
  // init the serial
    stdio_init_all();

    // Initialize SPI channel (channel, baud rate set to 20MHz)
    // connected to spi DAC
    spi_init(SPI_PORT, 20000000) ;
    // Format (channel, data bits per transfer, polarity, phase, order)
    spi_set_format(SPI_PORT, 16, 0, 0, 0);
    // Map SPI signals to GPIO ports
    //gpio_set_function(PIN_MISO, GPIO_FUNC_SPI);
    gpio_set_function(PIN_SCK, GPIO_FUNC_SPI);
    gpio_set_function(PIN_MOSI, GPIO_FUNC_SPI);
    gpio_set_function(PIN_CS, GPIO_FUNC_SPI) ;

    // Initialize VGA
    initVGA();

    ////////////////////////////////////////////////////////////////////////
    ///////////////////////// I2C CONFIGURATION ////////////////////////////

    i2c_init(I2C_CHAN, I2C_BAUD_RATE);
    gpio_set_function(SDA_PIN, GPIO_FUNC_I2C);
    gpio_set_function(SCL_PIN, GPIO_FUNC_I2C);
    gpio_pull_up(SDA_PIN);
    gpio_pull_up(SCL_PIN);

    // MPU6050 initialization
    mpu6050_reset();
    mpu6050_read_raw(acceleration, gyro);






    // connecting gpio2 to Vdd sets 'send' mode
    #define mode_sel 2
    gpio_init(mode_sel) ;	
    gpio_set_dir(mode_sel, GPIO_IN) ;
    // turn pulldown on
    gpio_set_pulls (mode_sel, false, true) ;

    int i;
    for (i=0; i<sin_table_len; i++) {
      // sine table is in 12 bit range
      sine_table[i] = (short)(2040 * sin(2*3.1416*(float)i/sin_table_len) + 2048) ;
    }
   
   // =======================
   // choose station vs access point
   // (receive vs send)
   int ap ;
   // jumper gpio 2 high for 'send' mode
   // start 'send' mode unit first!
   ap = gpio_get(mode_sel) ;
   //
   if(ap){
      mode = send ;
      TCP_SERVER_T *state = calloc(1, sizeof(TCP_SERVER_T));
    if (!state) {
        printf("failed to allocate state\n");
        return 1;
    }

    if (cyw43_arch_init()) {
        printf("failed to initialise\n");
        return 1;
    }

    // access point SSID and PASSWORD
    // WPA2 authorization
    const char *ap_name = "picow_test";
    const char *password = "password";

    cyw43_arch_enable_ap_mode(ap_name, password, CYW43_AUTH_WPA2_AES_PSK);

    // 'state' is a pointer to type TCP_SERVER_T 
    // set up the access point IP address and mask
    ip4_addr_t mask;
    IP4_ADDR(ip_2_ip4(&state->gw), 192, 168, 4, 1);
    IP4_ADDR(ip_2_ip4(&mask), 255, 255, 255, 0);

    //station address (as set below)
    sprintf(udp_target_pico,"%s", "192.168.4.10");

    #ifdef auto_setup
      paired = true ;
    #endif

    // Start the dhcp server
    // Even though in the porgram DHCP is not required, LWIP
    // seems to need it!
    // and set picoW IP address from 'state' structure
    // set 'mask' as defined above
    dhcp_server_t dhcp_server;
    dhcp_server_init(&dhcp_server, &state->gw, &mask);
    }
  
  else {
    mode = echo ;
    sleep_ms(1000) ;
    // =======================
  // init the staTION network
    if (cyw43_arch_init()) {
        printf("failed to initialise\n");
        return 1;
    }

    // hook up to local WIFI
    cyw43_arch_enable_sta_mode();

    // power managment 
    //cyw43_wifi_pm(&cyw43_state, CYW43_DEFAULT_PM & ~0xf);

    printf("Connecting to Wi-Fi...\n");
    if (cyw43_arch_wifi_connect_timeout_ms(WIFI_SSID, WIFI_PASSWORD, CYW43_AUTH_WPA2_AES_PSK, 30000)) {
        printf("failed to connect.\n");
        return 1;
    } else {
      // optional print addr
        //printf("Connected: picoW IP addr: %s\n", ip4addr_ntoa(netif_ip4_addr(netif_list)));
        // and use known ap target
        sprintf(udp_target_pico,"%s", "192.168.4.1");
        // set local addr by overridding DHCP
        ip_addr_t ip;
        IP4_ADDR(&ip, 192,168,4,10);
        netif_set_ipaddr(netif_default, &ip);
        //printf("modified: picoW IP addr: %s\n", ip4addr_ntoa(netif_ip4_addr(netif_list)));
        #ifdef auto_setup
          paired = true ;
          play = true ;
        #endif
    }

  }
  
    //============================
    // set up UDP recenve ISR handler
    udpecho_raw_init();

  // =====================================
  // init the thread control semaphores
  // for the send/receive
  // recv semaphone is set by an ISR
  PT_SEM_INIT(&new_udp_send_s, 0) ;
  PT_SEM_INIT(&new_udp_recv_s, 0) ;

  // =====================================
  // core 1
  // start core 1 threads
  multicore_reset_core1();
  multicore_launch_core1(&core1_main);

  // === config threads ========================
  // for core 0

  //printf("Starting threads\n") ;
  pt_add_thread(protothread_udp_recv);
  pt_add_thread(protothread_udp_send);
  pt_add_thread(protothread_serial);
  pt_add_thread(protothread_paddle1);
  pt_add_thread(protothread_ball1);
  pt_add_thread(protothread_score);
  //
  // === initalize the scheduler ===============
  pt_schedule_start ;

    cyw43_arch_deinit();
    return 0;
}