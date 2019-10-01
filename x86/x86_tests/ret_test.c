/*
  This file contains some functionality tests to assess properties of ret.
 */
#include<stdbool.h>
#include<stdint.h>
#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>

#include "utils.h"

void ret_noimm(uint64_t** ret, uint64_t* pre_rsp, uint64_t* post_rsp);
extern uint64_t ret_noimm_ret;

void ret_imm8(uint64_t** ret, uint64_t* pre_rsp, uint64_t* post_rsp);
extern uint64_t ret_imm8_ret;

void ret_imm8000(uint64_t** ret, uint64_t* pre_rsp, uint64_t* post_rsp);
extern uint64_t ret_imm8000_ret;

void ret_imm10000(uint64_t** ret, uint64_t* pre_rsp, uint64_t* post_rsp);
extern uint64_t ret_imm10000_ret;

int main(int argc, char** argv) {
    uint64_t* ret;
    uint64_t pre_rsp;
    uint64_t post_rsp;

    ret_noimm(&ret, &pre_rsp, &post_rsp);
    my_assert(ret == &ret_noimm_ret, "ret_noimm: Unexpected return\n");
    my_assert(post_rsp - pre_rsp == 0x08, "ret_noimm: Unexpected stack delta\n");

    ret_imm8(&ret, &pre_rsp, &post_rsp);
    my_assert(ret == &ret_imm8_ret, "ret_imm8: Unexpected return\n");
    my_assert(post_rsp - pre_rsp == 0x10, "ret_imm8: Unexpected stack delta\n");

    ret_imm8000(&ret, &pre_rsp, &post_rsp);
    my_assert(ret == &ret_imm8000_ret, "ret_imm8000: Unexpected return\n");
    my_assert(post_rsp - pre_rsp == 0x8008, "ret_imm8000: Unexpected stack delta\n");

    ret_imm10000(&ret, &pre_rsp, &post_rsp);
    my_assert(ret == &ret_imm10000_ret, "ret_imm10000: Unexpected return\n");
    my_assert(post_rsp - pre_rsp == 0x8, "ret_imm10000: Unexpected stack delta\n");

    return 0;
}
