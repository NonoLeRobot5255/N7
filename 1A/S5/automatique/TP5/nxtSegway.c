#include "tpl_os.h"
#include "nxt_motors.h"
#include "ecrobot_interface.h" 
#include "ecrobot_private.h"
#include "math.h"
#include "tools.h"    
#include "nxt_config.h"         

/* ------------------------------------------------------------------------ */
/*  Fonctions de configuration OSEK                                         */
/* ------------------------------------------------------------------------ */
FUNC(int, OS_APPL_CODE) main(void)
{   
    StartOS(OSDEFAULTAPPMODE);
    return 0;
}

DeclareTask(pendule);
DeclareTask(affichage);

DeclareAlarm(alarm_pendule);
DeclareAlarm(alarm_affichage);

/* ------------------------------------------------------------------------- */
/* Variables globales du système                                             */
/* ------------------------------------------------------------------------- */

/* Gyro calibration */
int  gyro_offset;                   /* gyroscope sensor offset value(deg)    */
int  gyro_offset_sum;               /* sum of gyroscope sensor offset 
				       value(deg)                            */
int  avg_cnt;                       /* average count to calculate 
				       gyro offset                           */

float xe[4] = {0.0,0.0,0.0,0.0};    /* equilibrium state                     */
float ue    = 0.0;                  /* command at equilibrium                */
float x[4];                         /* state                                 */
float y[2];                         /* observations                          */
float u;                            /* command of the controller (V)         */
float setpoint;                     /* target value for theta variable       */

float k[4] = {0.6700,  19.9053, 1.0747, 1.9614};

typedef enum {
  INIT_MODE,      /* system initialize mode */
  CAL_MODE,       /* gyro sensor offset calibration mode */
  CONTROL_MODE    /* balance and RC control mode */
} MODE_ENUM;
MODE_ENUM nxtSegway_mode= INIT_MODE;

void estimateur(double dt) {
    float teta=x[0];
  float psi=x[1];
  float teta_p=x[2];
  float psi_p=x[3];
  float teta_m=y[0];
  float psi_p2= y[1];
  float theta;
  x[3]=psi_p2;
  x[1]=psi+psi_p*dt;
  theta=teta_m+x[1];
  x[2]=(theta-x[0])/dt;
  x[0]=theta;
}

void controleur() {
  float s=0;
  for (int i=0;i<4; i++) {
    s = s + k[i]*(x[i]-xe[i]);
  }
  u = ue + s;
  
}

TASK(pendule) {
  float dt;
  int initial_time= 0;
        
  switch(nxtSegway_mode){
  
  case(INIT_MODE):

    nxt_motor_set_count(PORT_MOTOR_L, 0);   /* reset left motor count         */
    nxt_motor_set_count(PORT_MOTOR_R, 0);   /* reset right motor count        */

    /* Initial state */
    for(int i=0;i<4;i++){
      x[i] = xe[i];
    }

    /* target value */
    setpoint            = xe[0];
    
    initial_time= ecrobot_get_systick_ms();
    init_time(initial_time);
    
    /* Gyro calibration */
    gyro_offset         = 0;
    gyro_offset_sum     = 0;
    avg_cnt             = 0;
    
    nxtSegway_mode = CAL_MODE;
    
    break;

  case(CAL_MODE):

    gyro_offset_sum += (int) ecrobot_get_gyro_sensor(PORT_GYRO); 
    /* accumulation of the values given by the gyro */
    
    avg_cnt++;

    if ((ecrobot_get_systick_ms() - initial_time) >= 1500) {
      gyro_offset = gyro_offset_sum / avg_cnt;
      /* mean of the previous measures */
      
      ecrobot_sound_tone(440, 500, 30);       /* beep a tone                 */
      nxtSegway_mode = CONTROL_MODE;
    }

    break;

  case(CONTROL_MODE):
  y[1]=getGyro(gyro_offset);
    y[0]=getMotorAngle();
    dt=delta_t();
    estimateur(dt);
    controleur();
    nxt_motors_set_command(u);

    break;

  default:
    /* unexpected mode */
    nxt_motor_set_speed(PORT_MOTOR_L, 0, 1);
    nxt_motor_set_speed(PORT_MOTOR_R, 0, 1);
    break;
  }
  TerminateTask();
}


TASK(affichage) {
  /*display informations*/
  display_clear(0);

  //disp(1, " PWM  = ", (int)(pwmR+pwmL)/2);
  disp(2, " y[0] = ", (int)(y[0]*RAD2DEG));
  disp(3, " y[1] = ", (int)(y[1]*RAD2DEG));
  disp(4, " x[0] = ", (int)((x[0]) * RAD2DEG));
  disp(5, " x[1] = ", (int)((x[1]) * RAD2DEG));
  disp(6, " x[2] = ", (int)((x[2]) * RAD2DEG));
  disp(7, " x[3] = ", (int)((x[3]) * RAD2DEG));
  
  TerminateTask();
}

ISR(isr_button_start)
{
    ecrobot_status_monitor("isr_button_start");
    
}

ISR(isr_button_stop)
{
    ShutdownOS(E_OK);
}

ISR(isr_button_left)
{
    ecrobot_status_monitor("isr_button_left"); 

}

ISR(isr_button_right)
{
    ecrobot_status_monitor("isr_button_right");   

}
