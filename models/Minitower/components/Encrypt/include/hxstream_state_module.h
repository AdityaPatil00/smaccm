/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.3
 */
#ifndef __HXSTREAM_STATE_MODULE_H__
#define __HXSTREAM_STATE_MODULE_H__
#ifdef __cplusplus
extern "C" {
#endif
#include "ivory.h"
typedef struct hxstream_state { int32_t offset;
                                uint8_t fstate;
                                uint8_t ftag;
                                bool tagSeen;
} hxstream_state;
uint8_t decodeSM(struct hxstream_state *n_var0, uint8_t n_var1);

#ifdef __cplusplus
}
#endif
#endif /* __HXSTREAM_STATE_MODULE_H__ */