/* This file has been autogenerated by Ivory
 * Compiler version  0.1.0.3
 */
#include "user_input_result_types.h"

void user_input_result_get_le(const uint8_t *n_var0, uint32_t n_var1, struct user_input_result *n_var2)
{
    user_input_get_le(n_var0, n_var1, &n_var2->ui);
    control_source_t_get_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 16U), &n_var2->source);
    time_micros_t_get_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 17U), &n_var2->time);
}

void user_input_result_get_be(const uint8_t *n_var0, uint32_t n_var1, struct user_input_result *n_var2)
{
    user_input_get_be(n_var0, n_var1, &n_var2->ui);
    control_source_t_get_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 16U), &n_var2->source);
    time_micros_t_get_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 17U), &n_var2->time);
}

void user_input_result_set_le(uint8_t *n_var0, uint32_t n_var1, const struct user_input_result *n_var2)
{
    user_input_set_le(n_var0, n_var1, &n_var2->ui);
    control_source_t_set_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 16U), &n_var2->source);
    time_micros_t_set_le(n_var0, (uint32_t) (n_var1 + (uint32_t) 17U), &n_var2->time);
}

void user_input_result_set_be(uint8_t *n_var0, uint32_t n_var1, const struct user_input_result *n_var2)
{
    user_input_set_be(n_var0, n_var1, &n_var2->ui);
    control_source_t_set_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 16U), &n_var2->source);
    time_micros_t_set_be(n_var0, (uint32_t) (n_var1 + (uint32_t) 17U), &n_var2->time);
}