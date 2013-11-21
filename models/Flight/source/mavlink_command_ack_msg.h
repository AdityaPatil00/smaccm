/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.0
 */
#ifndef __MAVLINK_COMMAND_ACK_MSG_H__
#define __MAVLINK_COMMAND_ACK_MSG_H__
#ifdef __cplusplus
extern "C" {
#endif
#include "ivory.h"
#include "mavlinkSendModule.h"
#include "mavlink_pack_ivory.h"
struct command_ack_msg {
    uint16_t command;
    uint8_t result;
} __attribute__((__packed__));
void mavlink_command_ack_msg_send(const struct command_ack_msg* n_var0,
                                  uint8_t* n_var1, uint8_t n_var2[80U]);
void mavlink_command_ack_unpack(struct command_ack_msg* n_var0, const
                                uint8_t* n_var1);

#ifdef __cplusplus
}
#endif
#endif /* __MAVLINK_COMMAND_ACK_MSG_H__ */