/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.0
 */
#ifndef __MAVLINK_REQUEST_DATA_STREAM_MSG_H__
#define __MAVLINK_REQUEST_DATA_STREAM_MSG_H__
#ifdef __cplusplus
extern "C" {
#endif
#include "ivory.h"
#include "mavlinkSendModule.h"
#include "mavlink_pack_ivory.h"
struct request_data_stream_msg {
    uint16_t req_message_rate;
    uint8_t target_system;
    uint8_t target_component;
    uint8_t req_stream_id;
    uint8_t start_stop;
} __attribute__((__packed__));
void mavlink_request_data_stream_msg_send(const
                                          struct request_data_stream_msg* n_var0,
                                          uint8_t* n_var1, uint8_t n_var2[80U]);
void mavlink_request_data_stream_unpack(struct request_data_stream_msg* n_var0,
                                        const uint8_t* n_var1);

#ifdef __cplusplus
}
#endif
#endif /* __MAVLINK_REQUEST_DATA_STREAM_MSG_H__ */