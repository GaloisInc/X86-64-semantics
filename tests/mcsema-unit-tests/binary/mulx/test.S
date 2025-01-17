/*
 * Copyright (c) 2017 Trail of Bits, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

TEST_BEGIN(MULXedx, 2)
TEST_INPUTS(
    0, 0,
    1, 0x7FFF,
    1, 0xFFFF,
    0xFFFF, 0xFFFF,
    0xFFFFFFFF, 0xFFFF,
    0xFFFFFFFF, 0xFFFFFFFF)

    movl ARG1_32, %ecx
    movl ARG2_32, %ebx

    mulxl %ebx, %eax, %edx  
TEST_END

TEST_BEGIN_64(MULXrdx_64, 2)
TEST_INPUTS(
    0, 1,
    0xFFFF, 0xFFFF,
    0xFFFFFFFF, 0xFFFF,
    0xFFFFFFFF, 0xFFFFFFFF,
    0xFFFFFFFF, 0x7FFFFFFF,
    0x7FFFFFFF, 0xFFFFFFFF,
    0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF,
    0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)

    movq  ARG1_64, %rcx
    movq  ARG2_64, %rbx

    mulxq %rbx, %rax, %rdx
TEST_END_64
