/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.0
 */
#include "tower_task_usercode_userPPMInput_42.h"

uint16_t channels_49[8U];

struct userinput_result userinput_50;

struct flightmode flightmode_51;

void eventhandler_userPPMInput_42_per50_55(const uint32_t* n_var0)
{
    uint32_t n_deref0 = *n_var0;
    bool n_r1 = userinput_capture(channels_49);
    
    if (n_r1) {
        write_userPPMInput_42_dataport40_48(channels_49);
        
        bool n_r2 = deadManSwitch(channels_49);
        
        if (n_r2) {
            userinput_decode(channels_49, &userinput_50, n_deref0);
        }
    }
    userinput_failsafe(&userinput_50, n_deref0);
    write_userPPMInput_42_dataport36_46(&userinput_50);
    write_userPPMInput_42_dataport39_44(&flightmode_51);
}