/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.3
 */
#ifndef __FRAGMENT_0X200_MONITOR_H__
#define __FRAGMENT_0X200_MONITOR_H__
#ifdef __cplusplus
extern "C" {
#endif
#include "canDriverTypes.h"
#include "fragment_drop_monitor.h"
#include "ivory.h"
#include "ivory_serialize.h"
#include "smaccm_can_module.h"
#include "to_smaccm_can_monitor.h"
extern uint8_t fragment_sent_0x200;
extern uint8_t fragment_buf_0x200[80U];
extern bool fragment_aborting_0x200;
void callback_fragment_req_0x200(const uint8_t n_var0[80U]);
void callback_fragment_complete_0x200(const bool *n_var0);
void callback_fragment_abort_0x200(const bool *n_var0);

#ifdef __cplusplus
}
#endif
#endif /* __FRAGMENT_0X200_MONITOR_H__ */