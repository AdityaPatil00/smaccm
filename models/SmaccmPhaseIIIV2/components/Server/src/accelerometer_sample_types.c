/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.3
 */
#include "accelerometer_sample_types.h"

void accelerometer_sample_get_le(const uint8_t *n_var0, uint32_t n_var1, struct accelerometer_sample *n_var2)
{
    ibool_get_le(n_var0, n_var1, &n_var2->initfail);
    ibool_get_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 1U), &n_var2->samplefail);
    ibool_get_le(n_var0, (uint32_t) ((uint32_t) 2U + n_var1), &n_var2->calibrated);
    xyz_get_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 3U), &n_var2->sample);
    ivory_serialize_unpack_float_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 15U), &n_var2->temperature);
    time_micros_t_get_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 19U), &n_var2->time);
}

void accelerometer_sample_get_be(const uint8_t *n_var0, uint32_t n_var1, struct accelerometer_sample *n_var2)
{
    ibool_get_be(n_var0, n_var1, &n_var2->initfail);
    ibool_get_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 1U), &n_var2->samplefail);
    ibool_get_be(n_var0, (uint32_t) ((uint32_t) 2U + n_var1), &n_var2->calibrated);
    xyz_get_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 3U), &n_var2->sample);
    ivory_serialize_unpack_float_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 15U), &n_var2->temperature);
    time_micros_t_get_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 19U), &n_var2->time);
}

void accelerometer_sample_set_le(uint8_t *n_var0, uint32_t n_var1, const struct accelerometer_sample *n_var2)
{
    ibool_set_le(n_var0, n_var1, &n_var2->initfail);
    ibool_set_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 1U), &n_var2->samplefail);
    ibool_set_le(n_var0, (uint32_t) ((uint32_t) 2U + n_var1), &n_var2->calibrated);
    xyz_set_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 3U), &n_var2->sample);
    ivory_serialize_pack_float_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 15U), &n_var2->temperature);
    time_micros_t_set_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 19U), &n_var2->time);
}

void accelerometer_sample_set_be(uint8_t *n_var0, uint32_t n_var1, const struct accelerometer_sample *n_var2)
{
    ibool_set_be(n_var0, n_var1, &n_var2->initfail);
    ibool_set_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 1U), &n_var2->samplefail);
    ibool_set_be(n_var0, (uint32_t) ((uint32_t) 2U + n_var1), &n_var2->calibrated);
    xyz_set_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 3U), &n_var2->sample);
    ivory_serialize_pack_float_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 15U), &n_var2->temperature);
    time_micros_t_set_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 19U), &n_var2->time);
}