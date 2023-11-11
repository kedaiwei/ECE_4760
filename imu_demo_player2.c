/**
 * V. Hunter Adams (vha3@cornell.edu)
 *
 * This demonstration utilizes the MPU6050.
 * It gathers raw accelerometer/gyro measurements, scales
 * them, and plots them to the VGA display. The top plot
 * shows gyro measurements, bottom plot shows accelerometer
 * measurements.
 *

 * HARDWARE CONNECTIONS
 *  - GPIO 16 ---> VGA Hsync
 *  - GPIO 17 ---> VGA Vsync
 *  - GPIO 18 ---> 330 ohm resistor ---> VGA Red
 *  - GPIO 19 ---> 330 ohm resistor ---> VGA Green
 *  - GPIO 20 ---> 330 ohm resistor ---> VGA Blue
 *  - RP2040 GND ---> VGA GND
 *  - GPIO 8 ---> MPU6050 SDA
 *  - GPIO 9 ---> MPU6050 SCL
 *  - 3.3v ---> MPU6050 VCC
 *  - RP2040 GND ---> MPU6050 GND
 */

// Include standard libraries
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

// Include PICO libraries
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
#include "pt_cornell_rp2040_v1.h"

// Arrays in which raw measurements will be stored
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

fix15 paddle1_y = int2fix15(240);

fix15 paddle2_y = int2fix15(240);
fix15 paddle2_vy = float2fix15(0.5);
int player1;
int player2;
bool play = true;

// Interrupt service routine
static PT_THREAD(protothread_paddle2(struct pt *pt))
{
  PT_BEGIN(pt);
  while (true)
  {
    // wait for 0.1 sec
    PT_YIELD_usec(10);
    if (play)
    {
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
      paddle2_vy = 0 - multfix15((filtered_complementary - int2fix15(90)), float2fix15(0.005));

      if (paddle2_vy > float2fix15(0.9))
      {
        paddle2_vy = float2fix15(0.9);
      }
      if (paddle2_vy < float2fix15(-0.9))
      {
        paddle2_vy = float2fix15(-0.9);
      }

      // erase paddle
      fillRect(PADDLE2_X, fix2int15(paddle2_y), 10, PADDLE_LENGTH, BLACK);

      if (paddle2_y + paddle2_vy <= 0)
      {
        paddle2_y = 0;
      }
      else if (paddle2_y + paddle2_vy + int2fix15(PADDLE_LENGTH) >= int2fix15(VGA_BOTTOM))
      {
        paddle2_y = int2fix15(VGA_BOTTOM - PADDLE_LENGTH);
      }
      else
      {
        paddle2_y += paddle2_vy;
      }

      // draw paddle
      fillRect(PADDLE2_X, fix2int15(paddle2_y), 10, PADDLE_LENGTH, WHITE);
    }
  }
  PT_END(pt);
}

// Thread that draws to paddle1
static PT_THREAD(protothread_paddle1(struct pt *pt))
{
  // Indicate start of thread
  PT_BEGIN(pt);

  while (true)
  {
    PT_YIELD_usec(10);
    if (play)
    {
      // erase paddle
      fillRect(PADDLE1_X, fix2int15(paddle2_y), 10, PADDLE_LENGTH, BLACK);

      // draw paddle
      fillRect(PADDLE1_X, fix2int15(paddle2_y), 10, PADDLE_LENGTH, WHITE);
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
    PT_YIELD_usec(10);
    if (play)
    {
      // erase ball
      fillCircle(fix2int15(ball_x), fix2int15(ball_y), BALL_RADIUS, BLACK);

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
  while (1)
  {
    setCursor(100, 15);
    setTextSize(2);
    sprintf(str, "Player 1 = %d  ", player1);
    setTextColor2(WHITE, BLACK);
    writeString(str);

    setCursor(400, 15);
    sprintf(str, "Player 2 = %d  ", player2);
    setTextColor2(WHITE, BLACK);
    writeString(str);

    if (player1 == 10)
    {
      setCursor(200, 240);
      sprintf(str, "Player 1 wins!");
      setTextColor2(WHITE, BLACK);
      writeString(str);

      play = false;
    }

    if (player2 == 10)
    {
      setCursor(200, 240);
      sprintf(str, "Player 2 wins!");
      setTextColor2(WHITE, BLACK);
      writeString(str);
      play = false;
    }

    PT_YIELD_usec(100000);
  }
  PT_END(pt);
}

// Entry point for core 1
void core1_entry()
{
  pt_add_thread(protothread_paddle1);
  pt_schedule_start;
}

int main()
{
  // Initialize stdio
  stdio_init_all();

  // Initialize VGA
  initVGA();

  const uint RX_PIN = 1; // Choose the GPIO pin for RX
  uart_init(uart0, 9600);
  gpio_set_function(RX_PIN, GPIO_FUNC_UART);
  uart_set_hw_flow(uart0, false, false);
  uart_set_format(uart0, 8, 1, UART_PARITY_NONE);

  while (1)
  {
    while (uart_is_readable(uart0))
    {
      uint8_t ch = uart_getc(uart0);
      printf("Received: %c\n", ch);
    }
  }

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

  ////////////////////////////////////////////////////////////////////////
  ///////////////////////////// ROCK AND ROLL ////////////////////////////
  ////////////////////////////////////////////////////////////////////////

  // start core 1
  multicore_reset_core1();
  multicore_launch_core1(core1_entry);

  // start core 0
  pt_add_thread(protothread_paddle1);
  pt_add_thread(protothread_ball);
  pt_schedule_start;
}
