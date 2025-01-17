    .text
    .globl	strlen
strlen:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movq	$0, -8(%rbp)
    jmp	L2
L3:
    addq	$1, -8(%rbp)
L2:
    movq	-24(%rbp), %rdx
    movq	-8(%rbp), %rax
    addq	%rdx, %rax
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L3
    movq	-8(%rbp), %rax
    popq	%rbp
    ret
    .globl	strcpy
strcpy:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movq	%rsi, -32(%rbp)
    movq	-24(%rbp), %rax
    movq	%rax, -8(%rbp)
    nop
L6:
    movq	-24(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -24(%rbp)
    movq	-32(%rbp), %rdx
    leaq	1(%rdx), %rcx
    movq	%rcx, -32(%rbp)
    movzbl	(%rdx), %edx
    movb	%dl, (%rax)
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L6
    movq	-8(%rbp), %rax
    popq	%rbp
    ret
    .globl	strcmp
strcmp:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movq	%rsi, -16(%rbp)
    jmp	L9
L11:
    addq	$1, -8(%rbp)
    addq	$1, -16(%rbp)
L9:
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    testb	%al, %al
    je	L10
    movq	-8(%rbp), %rax
    movzbl	(%rax), %edx
    movq	-16(%rbp), %rax
    movzbl	(%rax), %eax
    cmpb	%al, %dl
    je	L11
L10:
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    movzbl	%al, %edx
    movq	-16(%rbp), %rax
    movzbl	(%rax), %eax
    movzbl	%al, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    popq	%rbp
    ret
    .globl	strchr
strchr:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movl	%esi, -12(%rbp)
    jmp	L14
L16:
    movq	-8(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -8(%rbp)
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L14
    movl	$0, %eax
    jmp	L15
L14:
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    movl	-12(%rbp), %edx
    cmpb	%dl, %al
    jne	L16
    movq	-8(%rbp), %rax
L15:
    popq	%rbp
    ret
    .globl	strncpy
strncpy:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movq	%rsi, -32(%rbp)
    movq	%rdx, -40(%rbp)
    movq	-24(%rbp), %rax
    movq	%rax, -8(%rbp)
L20:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L18
    movq	-8(%rbp), %rax
    jmp	L19
L18:
    movq	-24(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -24(%rbp)
    movq	-32(%rbp), %rdx
    leaq	1(%rdx), %rcx
    movq	%rcx, -32(%rbp)
    movzbl	(%rdx), %edx
    movb	%dl, (%rax)
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L20
    jmp	L21
L22:
    movq	-24(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -24(%rbp)
    movb	$0, (%rax)
L21:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L22
    movq	-8(%rbp), %rax
L19:
    popq	%rbp
    ret
    .globl	strncmp
strncmp:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movq	%rsi, -16(%rbp)
    movq	%rdx, -24(%rbp)
    jmp	L24
L26:
    movq	-8(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -8(%rbp)
    movzbl	(%rax), %ecx
    movq	-16(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -16(%rbp)
    movzbl	(%rax), %eax
    cmpb	%al, %cl
    je	L24
    movq	-8(%rbp), %rax
    subq	$1, %rax
    movzbl	(%rax), %eax
    movzbl	%al, %edx
    movq	-16(%rbp), %rax
    subq	$1, %rax
    movzbl	(%rax), %eax
    movzbl	%al, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    jmp	L25
L24:
    movq	-24(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -24(%rbp)
    testq	%rax, %rax
    jne	L26
    movl	$0, %eax
L25:
    popq	%rbp
    ret
    .globl	strrchr
strrchr:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movl	%esi, -28(%rbp)
    movq	$0, -8(%rbp)
L29:
    movq	-24(%rbp), %rax
    movzbl	(%rax), %eax
    movl	-28(%rbp), %edx
    cmpb	%dl, %al
    jne	L28
    movq	-24(%rbp), %rax
    movq	%rax, -8(%rbp)
L28:
    movq	-24(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -24(%rbp)
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L29
    movq	-8(%rbp), %rax
    popq	%rbp
    ret
    .globl	memcmp
memcmp:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movq	%rsi, -32(%rbp)
    movq	%rdx, -40(%rbp)
    movq	-24(%rbp), %rax
    movq	%rax, -16(%rbp)
    movq	-32(%rbp), %rax
    movq	%rax, -8(%rbp)
    jmp	L32
L35:
    movq	-16(%rbp), %rax
    movzbl	(%rax), %edx
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    cmpb	%al, %dl
    je	L33
    movq	-16(%rbp), %rax
    movzbl	(%rax), %eax
    movzbl	%al, %edx
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    movzbl	%al, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    jmp	L34
L33:
    addq	$1, -16(%rbp)
    addq	$1, -8(%rbp)
L32:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L35
    movl	$0, %eax
L34:
    popq	%rbp
    ret
    .globl	__stack_chk_fail
__stack_chk_fail:
    pushq	%rbp
    movq	%rsp, %rbp
    movq $-1, %rax
    jmp %rax
    
    nop
    popq	%rbp
    ret
    .globl	exit
exit:
    pushq	%rbp
    movq	%rsp, %rbp
    movl	%edi, -4(%rbp)
    movq $-1, %rax
    jmp %rax
    
    nop
    popq	%rbp
    ret
    .globl	abort
abort:
    pushq	%rbp
    movq	%rsp, %rbp
    movq $-1, %rax
    jmp %rax
    
    nop
    popq	%rbp
    ret
    .globl	memset
memset:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movl	%esi, -28(%rbp)
    movq	%rdx, -40(%rbp)
    movq	-24(%rbp), %rax
    movq	%rax, -8(%rbp)
    jmp	L40
L41:
    movq	-8(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -8(%rbp)
    movl	-28(%rbp), %edx
    movb	%dl, (%rax)
L40:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L41
    movq	-24(%rbp), %rax
    popq	%rbp
    ret
    .globl	memcpy
memcpy:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movq	%rsi, -32(%rbp)
    movq	%rdx, -40(%rbp)
    movq	-24(%rbp), %rax
    movq	%rax, -16(%rbp)
    movq	-32(%rbp), %rax
    movq	%rax, -8(%rbp)
    jmp	L44
L45:
    movq	-16(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -16(%rbp)
    movq	-8(%rbp), %rdx
    leaq	1(%rdx), %rcx
    movq	%rcx, -8(%rbp)
    movzbl	(%rdx), %edx
    movb	%dl, (%rax)
L44:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L45
    movq	-24(%rbp), %rax
    popq	%rbp
    ret
    .globl	free
free:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    nop
    popq	%rbp
    ret
    .globl	isprint
isprint:
    pushq	%rbp
    movq	%rsp, %rbp
    movl	%edi, -4(%rbp)
    cmpl	$96, -4(%rbp)
    jle	L49
    cmpl	$122, -4(%rbp)
    jg	L49
    movl	$1, %eax
    jmp	L50
L49:
    cmpl	$64, -4(%rbp)
    jle	L51
    cmpl	$90, -4(%rbp)
    jg	L51
    movl	$1, %eax
    jmp	L50
L51:
    cmpl	$47, -4(%rbp)
    jle	L52
    cmpl	$57, -4(%rbp)
    jg	L52
    movl	$1, %eax
    jmp	L50
L52:
    movl	$0, %eax
L50:
    popq	%rbp
    ret
    .comm	glob_int_arr,400,32
    .globl	glob_int
    .data
glob_int:
    .long	4
    .comm	glob_vol_int_arr,400,32
    .globl	glob_vol_ptr_int
glob_vol_ptr_int:
    .quad	glob_int_arr
    .globl	glob_ptr_vol_int
glob_ptr_vol_int:
    .quad	glob_vol_int_arr
    .globl	glob_vol_ptr_vol_int
glob_vol_ptr_vol_int:
    .quad	glob_vol_int_arr
    .comm	glob_vol_int,4,4
    .comm	stat_int_arr,400,32
    .comm	stat_vol_int_arr,400,32
stat_vol_ptr_int:
    .quad	stat_int_arr
stat_ptr_vol_int:
    .quad	stat_vol_int_arr
stat_vol_ptr_vol_int:
    .quad	stat_vol_int_arr
    .comm	stat_vol_int,4,4
    .comm	str,24,16
    .comm	vol_str,24,16
    .globl	vol_ptr_str
vol_ptr_str:
    .quad	str
    .globl	ptr_vol_str
ptr_vol_str:
    .quad	vol_str
    .globl	vol_ptr_vol_str
vol_ptr_vol_str:
    .quad	vol_str
    .text
    .globl	simple_vol_global
simple_vol_global:
    pushq	%rbp
    movq	%rsp, %rbp
    prefetchnta	glob_vol_int_arr(%rip)
    movq	glob_vol_ptr_int(%rip), %rax
    prefetchnta	(%rax)
    movq	glob_ptr_vol_int(%rip), %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_vol_int(%rip), %rax
    prefetchnta	(%rax)
    prefetchnta	glob_vol_int(%rip)
    nop
    popq	%rbp
    ret
    .globl	simple_vol_file
simple_vol_file:
    pushq	%rbp
    movq	%rsp, %rbp
    prefetchnta	stat_vol_int_arr(%rip)
    movq	stat_vol_ptr_int(%rip), %rax
    prefetchnta	(%rax)
    movq	stat_ptr_vol_int(%rip), %rax
    prefetchnta	(%rax)
    movq	stat_vol_ptr_vol_int(%rip), %rax
    prefetchnta	(%rax)
    prefetchnta	stat_vol_int(%rip)
    nop
    popq	%rbp
    ret
    .globl	expr_vol_global
expr_vol_global:
    pushq	%rbp
    movq	%rsp, %rbp
    prefetchnta	vol_str(%rip)
    movq	ptr_vol_str(%rip), %rax
    prefetchnta	(%rax)
    movq	vol_ptr_str(%rip), %rax
    prefetchnta	(%rax)
    movq	vol_ptr_vol_str(%rip), %rax
    prefetchnta	(%rax)
    prefetchnta	vol_str + 4(%rip)
    movq	ptr_vol_str(%rip), %rax
    addq	$4, %rax
    prefetchnta	(%rax)
    movq	vol_ptr_str(%rip), %rax
    addq	$4, %rax
    prefetchnta	(%rax)
    movq	vol_ptr_vol_str(%rip), %rax
    addq	$4, %rax
    prefetchnta	(%rax)
    prefetchnta	vol_str + 8(%rip)
    movq	vol_ptr_str(%rip), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    movq	ptr_vol_str(%rip), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    movq	vol_ptr_vol_str(%rip), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    movq	vol_str + 16(%rip), %rax
    prefetchnta	(%rax)
    movq	vol_ptr_str(%rip), %rax
    movq	16(%rax), %rax
    prefetchnta	(%rax)
    movq	ptr_vol_str(%rip), %rax
    movq	16(%rax), %rax
    prefetchnta	(%rax)
    movq	vol_ptr_vol_str(%rip), %rax
    movq	16(%rax), %rax
    prefetchnta	(%rax)
    movq	vol_str + 16(%rip), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    movq	vol_ptr_str(%rip), %rax
    movq	16(%rax), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    movq	ptr_vol_str(%rip), %rax
    movq	16(%rax), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    movq	vol_ptr_vol_str(%rip), %rax
    movq	16(%rax), %rax
    addq	$8, %rax
    prefetchnta	(%rax)
    prefetchnta	glob_vol_int_arr(%rip)
    movq	glob_vol_ptr_int(%rip), %rax
    prefetchnta	(%rax)
    movq	glob_ptr_vol_int(%rip), %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_vol_int(%rip), %rax
    prefetchnta	(%rax)
    prefetchnta	glob_vol_int_arr + 8(%rip)
    movq	glob_vol_ptr_int(%rip), %rax
    addq	$12, %rax
    prefetchnta	(%rax)
    movq	glob_ptr_vol_int(%rip), %rax
    addq	$12, %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_vol_int(%rip), %rax
    addq	$12, %rax
    prefetchnta	(%rax)
    movl	$glob_vol_int_arr + 12, %eax
    prefetchnta	(%rax)
    movl	glob_vol_int(%rip), %eax
    cltq
    salq	$2, %rax
    addq	$glob_vol_int_arr, %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_int(%rip), %rax
    addq	$20, %rax
    prefetchnta	(%rax)
    movq	glob_ptr_vol_int(%rip), %rax
    addq	$20, %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_vol_int(%rip), %rax
    addq	$20, %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_int(%rip), %rax
    movl	glob_vol_int(%rip), %edx
    movslq	%edx, %rdx
    salq	$2, %rdx
    addq	%rdx, %rax
    prefetchnta	(%rax)
    movq	glob_ptr_vol_int(%rip), %rax
    movl	glob_vol_int(%rip), %edx
    movslq	%edx, %rdx
    salq	$2, %rdx
    addq	%rdx, %rax
    prefetchnta	(%rax)
    movq	glob_vol_ptr_vol_int(%rip), %rax
    movl	glob_vol_int(%rip), %edx
    movslq	%edx, %rdx
    salq	$2, %rdx
    addq	%rdx, %rax
    prefetchnta	(%rax)
    nop
    popq	%rbp
    ret
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    movl	$0, %eax
    call	simple_vol_global
    movl	$0, %eax
    call	simple_vol_file
    movq	$str, str + 16(%rip)
    movq	$str, vol_str + 16(%rip)
    call	expr_vol_global
    movl	$0, %edi
    call	exit
