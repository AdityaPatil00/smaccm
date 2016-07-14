/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.3
 */
#ifndef __SEQUENCE_NUMBERED_ATT_CONTROL_DEBUG_TYPES_H__
#define __SEQUENCE_NUMBERED_ATT_CONTROL_DEBUG_TYPES_H__
#ifdef __cplusplus
extern "C" {
#endif
#include "att_control_debug_types.h"
#include "ivory.h"
#include "ivory_serialize.h"
#include "sequence_num_types.h"
typedef struct sequence_numbered_att_control_debug { uint32_t seqnum;
                                                     struct att_control_debug val;
} sequence_numbered_att_control_debug;
void sequence_numbered_att_control_debug_get_le(const uint8_t *n_var0, uint32_t n_var1, struct sequence_numbered_att_control_debug *n_var2);
void sequence_numbered_att_control_debug_get_be(const uint8_t *n_var0, uint32_t n_var1, struct sequence_numbered_att_control_debug *n_var2);
void sequence_numbered_att_control_debug_set_le(uint8_t *n_var0, uint32_t n_var1, const struct sequence_numbered_att_control_debug *n_var2);
void sequence_numbered_att_control_debug_set_be(uint8_t *n_var0, uint32_t n_var1, const struct sequence_numbered_att_control_debug *n_var2);

#ifdef __cplusplus
}
#endif
#endif /* __SEQUENCE_NUMBERED_ATT_CONTROL_DEBUG_TYPES_H__ */