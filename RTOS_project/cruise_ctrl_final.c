/* Cruise control skeleton for the IL 2206 embedded lab
 *
 * Maintainers:  Rodolfo Jordao (jordao@kth.se), George Ungereanu (ugeorge@kth.se)
 *
 * Description:
 *
 *   In this file you will find the "model" for the vehicle that is being simulated on top
 *   of the RTOS and also the stub for the control task that should ideally control its
 *   velocity whenever a cruise mode is activated.
 *
 *   The missing functions and implementations in this file are left as such for
 *   the students of the IL2206 course. The goal is that they get familiriazed with
 *   the real time concepts necessary for all implemented herein and also with Sw/Hw
 *   interactions that includes HAL calls and IO interactions.
 *
 *   If the prints prove themselves too heavy for the final code, they can
 *   be exchanged for alt_printf where hexadecimals are supported and also
 *   quite readable. This modification is easily motivated and accepted by the course
 *   staff.
 */
#include <stdio.h>
#include <string.h>
#include "system.h"
#include "includes.h"
#include "altera_avalon_pio_regs.h"
#include "sys/alt_irq.h" // it uses system clock for switches and buttons debounce
//#include "sys/alt_alarm.h"
#include "alt_types.h"
#include <stdlib.h> 
#include "ucos_ii.h"
#include <math.h>
#include <sys/alt_timestamp.h>

#define DEBUG 1

#define HW_TIMER_PERIOD 10 /* 100ms */
#define SYS_CLK 50000000
/* Button Patterns */

#define GAS_PEDAL_FLAG      0x08
#define BRAKE_PEDAL_FLAG    0x04
#define CRUISE_CONTROL_FLAG 0x02
/* Switch Patterns */

#define TOP_GEAR_FLAG       0x00000002
#define ENGINE_FLAG         0x00000001
#define SW_4                0x00000010
#define SW_5                0x00000020
#define SW_6                0x00000040
#define SW_7                0x00000080
#define SW_8                0x00000100
#define SW_9                0x00000200

/* LED Patterns */

#define LED_RED_0 0x00000001 // Engine
#define LED_RED_1 0x00000002 // Top Gear

#define LED_GREEN_0 0x0001 // Cruise Control activated
#define LED_GREEN_2 0x0002 // Cruise Control Button
#define LED_GREEN_4 0x0010 // Brake Pedal
#define LED_GREEN_6 0x0040 // Gas Pedal

/*
 * Definition of Tasks
 */

#define TASK_STACKSIZE 2048

OS_STK StartTask_Stack[TASK_STACKSIZE]; 
OS_STK ControlTask_Stack[TASK_STACKSIZE]; 
OS_STK VehicleTask_Stack[TASK_STACKSIZE];
OS_STK Switch_IO_data[TASK_STACKSIZE];
OS_STK Button_IO_data[TASK_STACKSIZE];
OS_STK Watchdog_data[TASK_STACKSIZE];
OS_STK Overload_data[TASK_STACKSIZE];
OS_STK Extraload_data[TASK_STACKSIZE];
// Task Priorities

#define STARTTASK_PRIO     5
#define Watchdog_PRIO     6
#define VEHICLETASK_PRIO  10
#define CONTROLTASK_PRIO  12
#define Switch_IO_PRIO  13
#define Button_IO_PRIO  14
#define Extraload_PRIO  15
#define Overload_PRIO  16
// Task Periods (multiples of 10 only)

#define Watchdog_PERIOD  350
#define CONTROL_PERIOD  300
#define VEHICLE_PERIOD  300
#define Switch_IO_PERIOD  100
#define Button_IO_PERIOD  100
#define Extraload_PERIOD  300
#define Overload_PERIOD  300
/*
 * Definition of Kernel Objects 
 */

// Mailboxes
OS_EVENT *Mbox_Throttle; //gas enum
OS_EVENT *Mbox_Velocity;
OS_EVENT *Mbox_Brake; // enum
OS_EVENT *Mbox_Engine; // enum
OS_EVENT *Mbox_Top_Gear; //enum
OS_EVENT *Mbox_Cruise_Ctrl; //enum
OS_EVENT *Mbox_Gas; //gas enum
OS_EVENT *Mbox_Switch;


// Semaphores
OS_EVENT *SyncSem_Veh,*SyncSem_Ctrl, *SyncSem_Switch_IO , *SyncSem_Button_IO, *Sync_Mbox_Sw,*Sync_Mbox_Bu, *SyncSem_WDog, *SyncSem_OV_Detect, *SyncSem_Extraload;
INT8U Sem_error_Veh, Sem_error_Ctrl, Sem_error_Switch_IO , Sem_error_Button_IO, Sem_error_Mbox_Sw, Sem_error_Mbox_Bu, Sem_error_WDog,Sem_error_OV_Detect,Sem_error_Extraload;


// SW-Timer
OS_TMR *Soft_timer_Veh_Ctrl;
INT8U err_Sft_Tmr;
BOOLEAN tmr_stat;

int count_signal_10ms=0; //helps find a period based on given task
char TMR_name[100]="Soft_time_global";
int ls_task[]={0,0,0,0,0,0}; // ctrl, vehicle, switch button
int arg=0;

void time_ISR_handler( ) {
    count_signal_10ms++;
    //printf("Timer ISR\n");
    if(((abs (count_signal_10ms -ls_task[0])) > (CONTROL_PERIOD / 10)))
    {
       Sem_error_Ctrl = OSSemPost(SyncSem_Ctrl);
		//printf("ctrl in queue\n");
		//Sem_error_Veh = OSSemPost(SyncSem_Veh);
    }
    
    if(((abs (count_signal_10ms - ls_task[1])) > (VEHICLE_PERIOD / 10)))
    {
		//printf("veh in queue\n");
      Sem_error_Veh = OSSemPost(SyncSem_Veh);
      //ls_task[1] = count_signal_10ms; 
    }
    if(((abs (count_signal_10ms - ls_task[2])) > (Switch_IO_PERIOD / 10)))
    {
      Sem_error_Switch_IO = OSSemPost(SyncSem_Switch_IO);
      //ls_task[2] = count_signal_10ms; 
    }
    if(((abs (count_signal_10ms - ls_task[3])) > (Button_IO_PERIOD / 10)))
    {
      Sem_error_Button_IO = OSSemPost(SyncSem_Button_IO);
      //ls_task[2] = count_signal_10ms; 
    }
    if(((abs (count_signal_10ms - ls_task[4])) > (Watchdog_PERIOD / 10)))
    {
      Sem_error_WDog = OSSemPost(SyncSem_WDog);
      //ls_task[2] = count_signal_10ms; 
    }
    if(((abs (count_signal_10ms - ls_task[5])) > (Overload_PERIOD / 10)))
    {
      Sem_error_OV_Detect = OSSemPost(SyncSem_OV_Detect);
      //ls_task[2] = count_signal_10ms; 
    }
    if(((abs (count_signal_10ms - ls_task[6])) > (Extraload_PERIOD / 10)))
    {
      //printf("Extra load Timer ISR\n");
      Sem_error_Extraload = OSSemPost(SyncSem_Extraload);
      //ls_task[2] = count_signal_10ms; 
    }



return;
}




/*
 * Types
 */
enum active {on = 2, off = 1};


/*
 * Global variables
 */ 
int delay;
INT16U led_green = 0; // Green LEDs
INT32U led_red = 0;   // Red LEDs
INT8U engine_lock= 0;
INT8U Watchdog_reset=1;
volatile int milliseconds;
/*
 * Helper functions
 */

int buttons_pressed(void)
{
  return ~IORD_ALTERA_AVALON_PIO_DATA(D2_PIO_KEYS4_BASE);    
}

int switches_pressed(void)
{
  return IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_TOGGLES18_BASE);    
}

/*
 * ISR for HW Timer
 */
void alarm_handler()
{
   OSTmrSignal();
  IOWR(TIMER_0_BASE, 0, 0);
    
    // Increment the global millisecond counter
}

static int b2sLUT[] = {0x40, //0
  0x79, //1
  0x24, //2
  0x30, //3
  0x19, //4
  0x12, //5
  0x02, //6
  0x78, //7
  0x00, //8
  0x18, //9
  0x3F, //-
};

/*
 * convert int to seven segment display format
 */
int int2seven(int inval){
  return b2sLUT[inval];
}

/*
 * output current velocity on the seven segement display
 */
void show_velocity_on_sevenseg(INT8S velocity){
  int tmp = velocity;
  int out;
  INT8U out_high = 0;
  INT8U out_low = 0;
  INT8U out_sign = 0;

  if(velocity < 0){
    out_sign = int2seven(10);
    tmp *= -1;
  }else{
    out_sign = int2seven(0);
  }

  out_high = int2seven(tmp / 10);
  out_low = int2seven(tmp - (tmp/10) * 10);

  out = int2seven(0) << 21 |
    out_sign << 14 |
    out_high << 7  |
    out_low;
  IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_HEX_LOW28_BASE,out);
}

/*
 * shows the target velocity on the seven segment display (HEX5, HEX4)
 * when the cruise control is activated (0 otherwise)
 */
void show_target_velocity(INT8U target_vel)
{

	int tmp =target_vel;
  int out;
  INT8U out_high = 0;
  INT8U out_low = 0;
  INT8U out_sign = 0;


  out_sign = int2seven(0);

  out_high = int2seven(tmp / 10);
  out_low = int2seven(tmp - (tmp/10) * 10);

  out = int2seven(0) << 21 |
    out_sign << 14 |
    out_high << 7  |
    out_low;
  IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_HEX_HIGH28_BASE,out);
  return;
}

/*
 * indicates the position of the vehicle on the track with the four leftmost red LEDs
 * LEDR17: [0m, 400m)
 * LEDR16: [400m, 800m)
 * LEDR15: [800m, 1200m)
 * LEDR14: [1200m, 1600m)
 * LEDR13: [1600m, 2000m)
 * LEDR12: [2000m, 2400m]
 */
void show_position(INT16U position)
{
   int LED_CTRL=0, posdata=0;
  if (position==0 || position<400)
  {
    posdata=0x00020000;
  }
  else if (position==400 || position<800)
  {
    posdata=0x00010000;
  }
  else if (position==800 || position<1200)
  {
    posdata=0x00008000;
  }
  else if (position==1200 || position<1600)
  {
    posdata=0x00004000;
  }
  else if (position==1600 || position<2000)
  {
    posdata=0x00002000;
  }
  else if (position==2000 || position<2400)
  {
    posdata=0x00001000;
  }
  else 
    posdata=0x00000000;
        LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_REDLED18_BASE);
        LED_CTRL= LED_CTRL & 0xFFF00FFF;
        LED_CTRL= LED_CTRL | posdata;
        IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_REDLED18_BASE, LED_CTRL);

  return;
}

/*
 * The task 'VehicleTask' is the model of the vehicle being simulated. It updates variables like
 * acceleration and velocity based on the input given to the model.
 * 
 * The car model is equivalent to moving mass with linear resistances acting upon it.
 * Therefore, if left one, it will stably stop as the velocity converges to zero on a flat surface.
 * You can prove that easily via basic LTI systems methods.
 */
void VehicleTask(void* pdata)
{ 
  // constants that should not be modified
  const unsigned int wind_factor = 1;
  const unsigned int brake_factor = 4;
  const unsigned int gravity_factor = 2;
  // variables relevant to the model and its simulation on top of the RTOS
  INT8U err;  
  void* msg;
  INT8U* throttle; 
  INT16S acceleration;  
  INT16U position = 0; 
  INT16S velocity = 0;
  enum active *brake_pedal;
  enum active *engine;

  printf("Vehicle task created!\n");

  while(1)
  {
     OSSemPend(SyncSem_Veh, 0, &Sem_error_Veh); 

    err = OSMboxPost(Mbox_Velocity, (void *) &velocity);

    // OSTimeDlyHMSM(0,0,0, VEHICLE_PERIOD);


    /* Non-blocking read of mailbox: 
       - message in mailbox: update throttle
       - no message:         use old throttle
       */

    msg = OSMboxPend(Mbox_Throttle, 100, &err); 
    if (err == OS_NO_ERR) 
    {
      throttle = (INT8U*) msg;
      //printf("throttle: %d \n", *throttle);
    }
    /* Same for the brake signal that bypass the control law */
    msg = OSMboxPend(Mbox_Brake, 100, &err); 
    if (err == OS_NO_ERR) 
    // {
      brake_pedal = (enum active*) msg;
    //   if(*brake_pedal==on)
    //   printf("brake: on \n" );
		// else printf("brake: no in mailbox \n" );
    //   }
    /* Same for the engine signal that bypass the control law */
    msg = OSMboxPend(Mbox_Engine, 100, &err); 
    if (err == OS_NO_ERR) 
    // {
      engine = (enum active*) msg;
      // if (*engine==on)
      // printf("engine: on from mailbox \n" );
      // }


    // vehichle cannot effort more than 80 units of throttle
    if (*throttle > 80) *throttle = 80;

    // brakes + wind
    if (*brake_pedal == off)
    {
      // wind resistance
      acceleration = - wind_factor*velocity;
      // actuate with engines
      if (*engine == on)
        acceleration += (*throttle);

      // gravity effects
      if (400 <= position && position < 800)
        acceleration -= gravity_factor; // traveling uphill
      else if (800 <= position && position < 1200)
        acceleration -= 2*gravity_factor; // traveling steep uphill
      else if (1600 <= position && position < 2000)
        acceleration += 2*gravity_factor; //traveling downhill
      else if (2000 <= position)
        acceleration += gravity_factor; // traveling steep downhill
    }
    // if the engine and the brakes are activated at the same time,
    // we assume that the brake dynamics dominates, so both cases fall
    // here.
    else 
    acceleration = - brake_factor*velocity;
	  printf("Position: %d m\n", position);
    printf("Velocity: %d m/s\n", velocity);
    printf("Accell: %d m/s2\n", acceleration);
    printf("Throttle: %d V\n", *throttle);

    position = position + velocity * VEHICLE_PERIOD / 1000;
    velocity = velocity  + acceleration * VEHICLE_PERIOD / 1000.0;
    // reset the position to the beginning of the track
    
    show_position(position);

    if(position > 2400)
      position = 0;

    show_velocity_on_sevenseg((INT8S) velocity);
	ls_task[1] = count_signal_10ms; 
  }
} 

/*
 * The task 'ControlTask' is the main task of the application. It reacts
 * on sensors and generates responses.
 */

void ControlTask(void* pdata)
{
  
  static enum active Cruise_ctrl_mode_1 = off;
  INT8U err;
  int throttle_calc;
  INT8U throttle = 40; /* Value between 0 and 80, which is interpreted as between 0.0V and 8.0V */
  void* msg;
  INT16S* current_velocity;
  static INT16S cruise_ctrl_vel=0; 
  enum active *Engine_sw = off, *Top_Gear_sw = off, *gas_pedal = off;
  enum active *brake_pedal = off;
  enum active *cruise_control = off;
  int LED_CTRL; 
  msg = OSMboxPend(Mbox_Brake, 100, &err); 
    if (err == OS_NO_ERR) 
      brake_pedal = (enum active*) msg;

  while(1)
  {   
    //OSSemPend(SyncSem_Veh, 0, &Sem_error_Veh);

	OSSemPend(SyncSem_Ctrl, 0, &Sem_error_Ctrl); 
  //printf("Control Task created!\n");

  // data acquisition
	 
    msg = OSMboxPend(Mbox_Velocity, 100, &err);
    current_velocity = (INT16S*) msg;

    msg = OSMboxPend(Mbox_Brake, 100, &err); 
    if (err == OS_NO_ERR) 
      	brake_pedal = (enum active*) msg;

    
    msg = OSMboxPend(Mbox_Engine, 100, &err); 
    if (err == OS_NO_ERR)
      Engine_sw = (enum active*) msg;

    msg = OSMboxPend(Mbox_Top_Gear, 100, &err); 
    if (err == OS_NO_ERR) 
      Top_Gear_sw = (enum active*) msg;

    msg = OSMboxPend(Mbox_Gas, 100, &err); 
    if (err == OS_NO_ERR) 
      gas_pedal = (enum active*) msg;
		

    msg = OSMboxPend(Mbox_Cruise_Ctrl, 100, &err); 
    if (err == OS_NO_ERR) {
        cruise_control = (enum active*) msg;
        }

		if(*current_velocity !=0 && *Engine_sw==off)
    {
        //Override_sw
        //declare a global variable to lock engine turnoff;
        engine_lock=1;
        LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_REDLED18_BASE);
        LED_CTRL= LED_CTRL | ENGINE_FLAG;
        IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_REDLED18_BASE, LED_CTRL);
    }
    if (*current_velocity ==0 && *Engine_sw==on || *current_velocity !=0 && *Engine_sw==on || *current_velocity ==0 && *Engine_sw==off)
    {
    engine_lock=0;
    }
    


    if(Cruise_ctrl_mode_1==off)
    {
        printf("CC_mode_off");
		throttle=40;
    }
    else printf("CC_mode_on");
    
    if(*cruise_control==on)
    {
        if(*Engine_sw==on && *Top_Gear_sw == on && *brake_pedal==off && *gas_pedal == off && *current_velocity >= 20 && Cruise_ctrl_mode_1==off)
        {
            // Turn on cruise_ctrl
            Cruise_ctrl_mode_1=on;
            //turn on LED
          LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE);
        	LED_CTRL= LED_CTRL | LED_GREEN_0;
        	IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE, LED_CTRL);
            // define display target velocity on 7 segment display
          cruise_ctrl_vel = *current_velocity;
          show_target_velocity(cruise_ctrl_vel);
        }
        if(*Engine_sw==off || *Top_Gear_sw == off || *brake_pedal==on || *gas_pedal == on)
        {
          // printf("CC_Off");
          LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE);
        	LED_CTRL= LED_CTRL & ~LED_GREEN_0;
        	IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE, LED_CTRL);
          Cruise_ctrl_mode_1=off;    
          show_target_velocity(0);    
        }
    }
    if(*cruise_control==off && Cruise_ctrl_mode_1==on)
    {
          LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE);
        	LED_CTRL= LED_CTRL & ~LED_GREEN_0;
        	IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE, LED_CTRL);
          Cruise_ctrl_mode_1=off;
          show_target_velocity(0); 
    }

    if(Cruise_ctrl_mode_1==on)
    {
      LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE);
      LED_CTRL= LED_CTRL | LED_GREEN_0;
      IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE, LED_CTRL);
      //Control law
      if(*current_velocity - cruise_ctrl_vel >= 7)
      {
          // fast decelarataion
          throttle_calc= (int)(*current_velocity - cruise_ctrl_vel*1000)/CONTROL_PERIOD;
          throttle_calc=(throttle_calc+16)/2;
      }
      else if(*current_velocity - cruise_ctrl_vel >=5)
      {
          throttle_calc= (int)(*current_velocity - cruise_ctrl_vel*1000)/CONTROL_PERIOD;
          throttle_calc=(throttle_calc+24)/2;
      }
      else if(*current_velocity - cruise_ctrl_vel >=3)
      {
          throttle_calc= (int)(*current_velocity - cruise_ctrl_vel*1000)/CONTROL_PERIOD;
          throttle_calc=(throttle_calc+32)/2;
      }
      else if(abs(*current_velocity - cruise_ctrl_vel) >= 2 )
      {
            throttle_calc=40;
      }
      else if(cruise_ctrl_vel - *current_velocity >= 3)
      {
          throttle_calc= (int)(*current_velocity - cruise_ctrl_vel*1000)/CONTROL_PERIOD;
          throttle_calc=(throttle_calc+48)/2;
      }
      else if(cruise_ctrl_vel - *current_velocity >= 5)
      {
          throttle_calc= (int)(*current_velocity - cruise_ctrl_vel*1000)/CONTROL_PERIOD;
          throttle_calc=(throttle_calc+56)/2;
      }
      else if(cruise_ctrl_vel - *current_velocity >= 7)
      {
          throttle_calc= (int)(*current_velocity - cruise_ctrl_vel*1000)/CONTROL_PERIOD;
          throttle_calc=(throttle_calc+64)/2;
          throttle=(INT8U)throttle_calc;
      }
      else 
      throttle_calc=40;
      
      if(throttle_calc>80)
      throttle=80;
      else if(throttle_calc<0)
      throttle=0;
      else throttle=(INT8U)throttle_calc;
      
    }
    

  err = OSMboxPost(Mbox_Throttle, (void *) &throttle);
	ls_task[0] = count_signal_10ms;
  }
}

void Switch_IO_Task(void* pdata)
{
    INT8U err,i;
    int LED_CTRL;
    int sw_status, raw_eng, raw_top_gear, LED_data=0, sw_aray[6]={0}, sw_sts_value;
    IOWR_ALTERA_AVALON_PIO_DIRECTION(DE2_PIO_REDLED18_BASE, 0xFFFFFFFF);
    enum active Engine_sw = off, Top_Gear_sw = off;
  while(1)
  {   
    //OSSemPend(SyncSem_Veh, 0, &Sem_error_Veh);
	OSSemPend(SyncSem_Switch_IO, 0, &Sem_error_Switch_IO); 
  	//printf("Switch_IO Task created!\n"); 
    sw_status= switches_pressed();
    //printf("pressed values: %d\n",sw_status); 
    raw_eng = sw_status & ENGINE_FLAG;
        if(raw_eng == 1)
        {
           // printf("engine is ON \n");
            Engine_sw = on;
        }
        else
        {
           // printf("engine is OFF \n");
            Engine_sw = off;
		    }
    raw_top_gear = sw_status & TOP_GEAR_FLAG;
    if(raw_top_gear == 2)
    {
		//Top_gear is ON
        //printf("top gear is ON \n");
        Top_Gear_sw = on;
    }
    else
    {
       // printf("top gear is OFF \n");
        Top_Gear_sw = off;
    }


if(engine_lock==0)
{
    if(raw_eng==1)
    {
        if(raw_top_gear==0)
        {
            LED_data= LED_RED_0;
        }
        else
        {
            LED_data= LED_RED_0 | LED_RED_1;
        }
    }
    else
    {
        if(raw_top_gear==0)
        {
            LED_data= 0;
        }
        else
        {
            LED_data= LED_RED_1;
        }
    }
}
else {
    if(raw_top_gear==0)
    {
      LED_data= LED_RED_0;
    }
    else
    {
       LED_data= LED_RED_0 | LED_RED_1;
    }

}

        LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_REDLED18_BASE);
        LED_CTRL= LED_CTRL & 0xFFFFFFFC;
        LED_CTRL= LED_CTRL | LED_data;
        IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_REDLED18_BASE, LED_CTRL);
	      
      sw_aray[5]=sw_status & SW_4;
      sw_aray[4]=sw_status & SW_5;
      sw_aray[3]=sw_status & SW_6;
      sw_aray[2]=sw_status & SW_7;
      sw_aray[1]=sw_status & SW_8;
      sw_aray[0]=sw_status & SW_9;
      
      
      sw_sts_value=0;  
      for(i=0;i<6;+i++)
      {
          sw_sts_value= sw_sts_value | (sw_aray[i]);
      }  
        sw_sts_value=sw_sts_value>>4;
        ls_task[2] = count_signal_10ms;
    // OSTimeDlyHMSM(0,0,0, CONTROL_PERIOD);    
  
    err = OSMboxPost(Mbox_Engine, (void *) &Engine_sw);
    err = OSMboxPost(Mbox_Top_Gear, (void *) &Top_Gear_sw);
    err = OSMboxPost(Mbox_Switch, (void *) &sw_sts_value);
    }
  
}



void Button_IO_Task(void* pdata)
{
    INT8U err,LED_CTRL;
    int raw_button[3]={0}; // cruise ctrl, brake, gas,
    int button_status,i;  
    int LED_data[3]={0}, led_data_final=0;
    enum active BRAKE_PEDAL=off, GAS_PEDAL=off, Cruise_ctrl=off;


    IOWR_ALTERA_AVALON_PIO_DIRECTION(DE2_PIO_GREENLED9_BASE, 0xFFFFFFFF);
  while(1)
  {   
    //OSSemPend(SyncSem_Veh, 0, &Sem_error_Veh);
	  OSSemPend(SyncSem_Button_IO, 0, &Sem_error_Button_IO); 
  	//printf("Switch_IO Task created!\n"); 
    button_status= buttons_pressed() + 16;
    //printf("pressed values: %d\n",button_status); 
    
    
  // gas pedal
     raw_button[2]= button_status & GAS_PEDAL_FLAG;  //8
  // brake pedal
     raw_button[1]= button_status & BRAKE_PEDAL_FLAG; //4
  // cruise control pedal
     raw_button[0]= button_status & CRUISE_CONTROL_FLAG; //2
    
    
    // for(i=0;i<3;i++)
    // {
    //     if(raw_button[i] == pow(2,(i+1)))
    //     {
    //        // printf("button %d is ON \n",(i+1));
    //     }
    //     else
    //     {
    //        // printf("button %d is OFF \n",(i+1));
    //     }
    // }
     
    led_data_final=0;
    for( i=0;i<3;i++)
    {
        if (raw_button[i] == pow(2,(i+1)))
        {
            LED_data[i]=pow(2,(2*i+2));
            led_data_final=led_data_final | LED_data[i];
        }
        else
        {   
            LED_data[i]=0;
            led_data_final=led_data_final | LED_data[i];
        }
    } 

    LED_CTRL=IORD_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE);
    LED_CTRL= LED_CTRL & LED_GREEN_0;
    led_data_final=led_data_final | LED_CTRL;
    IOWR_ALTERA_AVALON_PIO_DATA(DE2_PIO_GREENLED9_BASE, led_data_final);  
    ls_task[3] = count_signal_10ms;
    
    if(raw_button[0]==2)
    {
        Cruise_ctrl = on;
        err = OSMboxPost(Mbox_Cruise_Ctrl, (void *) &Cruise_ctrl);
    }
    else
    {
        Cruise_ctrl = off;
        err = OSMboxPost(Mbox_Cruise_Ctrl, (void *) &Cruise_ctrl);
    }

    if(raw_button[1]==4)
    {
        BRAKE_PEDAL = on;
        err = OSMboxPost(Mbox_Brake, (void *) &BRAKE_PEDAL);
    }
    else
    {
        BRAKE_PEDAL = off;
        err = OSMboxPost(Mbox_Brake, (void *) &BRAKE_PEDAL);
    }

    if(raw_button[2]==8)
    {
        GAS_PEDAL = on;
        err = OSMboxPost(Mbox_Throttle, (void *) &GAS_PEDAL);
    }
    else
    {
        GAS_PEDAL = off;
        err = OSMboxPost(Mbox_Gas, (void *) &GAS_PEDAL);
    }
    
    // OSTimeDlyHMSM(0,0,0, CONTROL_PERIOD);
  }
}

void Watchdog_task(void* pdata)
{
  while(1)
  {
    OSSemPend(SyncSem_WDog, 0, &Sem_error_WDog); 
    //printf("WDog");
    if(Watchdog_reset==1)
    {
      Watchdog_reset=0;
    }
    else
    {
      printf("\n\n\n*******************System overload****************\n\n\n");
    }

    ls_task[4] = count_signal_10ms;
  }
}


void Overload_task(void* pdata)
{
   while(1)
  {
    
    OSSemPend(SyncSem_OV_Detect, 0, &Sem_error_OV_Detect); 
      //printf("OV_Det");
      Watchdog_reset=1;
    ls_task[5] = count_signal_10ms;
  }

}


void Extraload_task(void* pdata)
{
  INT8U err, sw_data_used;
  void* msg;
  int *switch_data;double delay_ticks=0, i;
   while(1)
  {
    OSSemPend(SyncSem_Extraload, 0, &Sem_error_Extraload); 

    
    msg = OSMboxPend(Mbox_Switch, 100, &err);
    switch_data = (int*) msg;
    sw_data_used=*switch_data;
    printf("\nExtraload percentage : %d\n\n",(*switch_data)*2);
    if (sw_data_used > 50)
    {
      sw_data_used = 50;
    }
    delay_ticks= (50000000*300*sw_data_used*2)/100000;
    for(i=0;i<delay_ticks;i++);
    //Comp delay

    ls_task[6] = count_signal_10ms;
  }

}


/* 
 * The task 'StartTask' creates all other tasks kernel objects and
 * deletes itself afterwards.
 */ 

void StartTask(void* pdata)
{
  INT8U err;
  void* context;

  //static alt_alarm alarm;     /* Is needed for timer ISR function */
  SyncSem_Veh=OSSemCreate(1);
  SyncSem_Ctrl=OSSemCreate(1);
  SyncSem_Switch_IO=OSSemCreate(1);
  SyncSem_Button_IO=OSSemCreate(1);
  SyncSem_WDog=OSSemCreate(1);
  SyncSem_OV_Detect=OSSemCreate(1);
  SyncSem_Extraload=OSSemCreate(1);
  

  /* Base resolution for SW timer : HW_TIMER_PERIOD ms */
  delay = alt_timestamp_freq() * HW_TIMER_PERIOD / 1000; 
  printf("delay in ticks %d\n", delay);

  void init_timer() {
    // Disable the timer (control register)
    IOWR(TIMER_0_BASE, 1, 0);
    
    // Set the timer period (for 10 ms)
    IOWR(TIMER_0_BASE, 2, delay);
    
    // Enable continuous mode and interrupt
    IOWR(TIMER_0_BASE, 1, 7);  // bit 2: CONT (continuous), bit 1: ITO (interrupt on timeout), bit 0: START

    // Register the timer ISR
    alt_irq_register(TIMER_0_IRQ, NULL, alarm_handler);
}
  
  /* 
   * Create Hardware Timer with a period of 'delay' 
   */
  if (alt_timestamp_start() < 0) {
        printf("No timestamp device available!\n");
        return;
    }

  /* 
   * Create and start Software Timer 
   */

  /*
   * Creation of Kernel Objects
   */

  // Mailboxes
  Mbox_Throttle = OSMboxCreate((void*) 0); /* Empty Mailbox - Throttle */
  Mbox_Velocity = OSMboxCreate((void*) 0); /* Empty Mailbox - Velocity */
  Mbox_Brake = OSMboxCreate((void*) 0); /* Empty Mailbox - Velocity */
  Mbox_Engine = OSMboxCreate((void*) 0); /* Empty Mailbox - Engine */
  Mbox_Gas = OSMboxCreate((void*) 0); /* Empty Mailbox - Velocity */
  Mbox_Top_Gear = OSMboxCreate((void*) 0); /* Empty Mailbox - Engine */
  Mbox_Cruise_Ctrl = OSMboxCreate((void*) 0);
  Mbox_Switch = OSMboxCreate((void*) 0);
  
  /*
   * Create statistics task
   */

  OSStatInit();
  init_timer();
  /* 
   * Creating Tasks in the system 
   */
Soft_timer_Veh_Ctrl = OSTmrCreate( 0,10,OS_TMR_OPT_PERIODIC,time_ISR_handler,(void*)&arg,(INT8U *) &TMR_name[0],&err_Sft_Tmr);
tmr_stat=  OSTmrStart(Soft_timer_Veh_Ctrl,  
                            &err_Sft_Tmr); 
               
  err = OSTaskCreateExt(
      ControlTask, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &ControlTask_Stack[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      CONTROLTASK_PRIO,
      CONTROLTASK_PRIO,
      (void *)&ControlTask_Stack[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);

  err = OSTaskCreateExt(
      VehicleTask, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &VehicleTask_Stack[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      VEHICLETASK_PRIO,
      VEHICLETASK_PRIO,
      (void *)&VehicleTask_Stack[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);

  err = OSTaskCreateExt(
      Switch_IO_Task, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &Switch_IO_data[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      Switch_IO_PRIO,
      Switch_IO_PRIO,
      (void *)&Switch_IO_data[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);

  err = OSTaskCreateExt(
      Button_IO_Task, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &Button_IO_data[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      Button_IO_PRIO,
      Button_IO_PRIO,
      (void *)&Button_IO_data[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);

  
  err = OSTaskCreateExt(
      Watchdog_task, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &Watchdog_data[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      Watchdog_PRIO,
      Watchdog_PRIO,
      (void *)&Watchdog_data[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);

err = OSTaskCreateExt(
      Overload_task, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &Overload_data[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      Overload_PRIO,
      Overload_PRIO,
      (void *)&Overload_data[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);

  err = OSTaskCreateExt(
      Extraload_task, // Pointer to task code
      NULL,        // Pointer to argument that is
      // passed to task
      &Extraload_data[TASK_STACKSIZE-1], // Pointer to top
      // of task stack
      Extraload_PRIO,
      Extraload_PRIO,
      (void *)&Extraload_data[0],
      TASK_STACKSIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK);
  printf("All Tasks and Kernel Objects generated!\n");

  /* Task deletes itself */

  OSTaskDel(OS_PRIO_SELF);
}

/*
 *
 * The function 'main' creates only a single task 'StartTask' and starts
 * the OS. All other tasks are started from the task 'StartTask'.
 *
 */

int main(void) {

  printf("Lab: Cruise Control\n");

  OSTaskCreateExt(
      StartTask, // Pointer to task code
      NULL,      // Pointer to argument that is
      // passed to task
      (void *)&StartTask_Stack[TASK_STACKSIZE-1], // Pointer to top
      // of task stack 
      STARTTASK_PRIO,
      STARTTASK_PRIO,
      (void *)&StartTask_Stack[0],
      TASK_STACKSIZE,
      (void *) 0,  
      OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR);

  OSStart();

  return 0;
}
