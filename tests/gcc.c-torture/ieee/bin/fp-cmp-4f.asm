    .text
    .globl	strchr
strchr:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movl	%esi, -12(%rbp)
    nop
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    movl	-12(%rbp), %edx
    cmpb	%dl, %al
    je	L6
    movq	-8(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -8(%rbp)
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L3
    movl	$0, %eax
    jmp	L1
L3:
    movq	-8(%rbp), %rax
    jmp	L1
L6:
L1:
    popq	%rbp
    ret
    .globl	strlen
strlen:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -24(%rbp)
    movq	$0, -8(%rbp)
    jmp	L8
L9:
    addq	$1, -8(%rbp)
L8:
    movq	-24(%rbp), %rdx
    movq	-8(%rbp), %rax
    addq	%rdx, %rax
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L9
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
L12:
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
    jne	L12
    movq	-8(%rbp), %rax
    popq	%rbp
    ret
    .globl	strcmp
strcmp:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movq	%rsi, -16(%rbp)
    jmp	L15
L17:
    addq	$1, -8(%rbp)
    addq	$1, -16(%rbp)
L15:
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    testb	%al, %al
    je	L16
    movq	-8(%rbp), %rax
    movzbl	(%rax), %edx
    movq	-16(%rbp), %rax
    movzbl	(%rax), %eax
    cmpb	%al, %dl
    je	L17
L16:
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
    jmp	L20
L23:
    movq	-16(%rbp), %rax
    movzbl	(%rax), %edx
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    cmpb	%al, %dl
    je	L21
    movq	-16(%rbp), %rax
    movzbl	(%rax), %eax
    movzbl	%al, %edx
    movq	-8(%rbp), %rax
    movzbl	(%rax), %eax
    movzbl	%al, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    jmp	L22
L21:
    addq	$1, -16(%rbp)
    addq	$1, -8(%rbp)
L20:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L23
    movl	$0, %eax
L22:
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
    jmp	L28
L29:
    movq	-8(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -8(%rbp)
    movl	-28(%rbp), %edx
    movb	%dl, (%rax)
L28:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L29
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
    jmp	L32
L33:
    movq	-16(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -16(%rbp)
    movq	-8(%rbp), %rdx
    leaq	1(%rdx), %rcx
    movq	%rcx, -8(%rbp)
    movzbl	(%rdx), %edx
    movb	%dl, (%rax)
L32:
    movq	-40(%rbp), %rax
    leaq	-1(%rax), %rdx
    movq	%rdx, -40(%rbp)
    testq	%rax, %rax
    jne	L33
    movq	-24(%rbp), %rax
    popq	%rbp
    ret
    .globl	malloc
malloc:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movl	$1000, %eax
    popq	%rbp
    ret
    .globl	calloc
calloc:
    pushq	%rbp
    movq	%rsp, %rbp
    movq	%rdi, -8(%rbp)
    movq	%rsi, -16(%rbp)
    movl	$1000, %eax
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
    jle	L41
    cmpl	$122, -4(%rbp)
    jg	L41
    movl	$1, %eax
    jmp	L42
L41:
    cmpl	$64, -4(%rbp)
    jle	L43
    cmpl	$90, -4(%rbp)
    jg	L43
    movl	$1, %eax
    jmp	L42
L43:
    cmpl	$47, -4(%rbp)
    jle	L44
    cmpl	$57, -4(%rbp)
    jg	L44
    movl	$1, %eax
    jmp	L42
L44:
    movl	$0, %eax
L42:
    popq	%rbp
    ret
    .globl	test_isunordered
test_isunordered:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    movl	%edi, -12(%rbp)
    vmovss	-4(%rbp), %xmm0
    vucomiss	-8(%rbp), %xmm0
    jnp	L46
    cmpl	$0, -12(%rbp)
    jne	L48
    call	abort
L46:
    cmpl	$0, -12(%rbp)
    je	L48
    call	abort
L48:
    nop
    leave
    ret
    .globl	test_isless
test_isless:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    movl	%edi, -12(%rbp)
    vmovss	-8(%rbp), %xmm0
    vucomiss	-4(%rbp), %xmm0
    setbe	%al
    xorl	$1, %eax
    testb	%al, %al
    je	L50
    cmpl	$0, -12(%rbp)
    jne	L52
    call	abort
L50:
    cmpl	$0, -12(%rbp)
    je	L52
    call	abort
L52:
    nop
    leave
    ret
    .globl	test_islessequal
test_islessequal:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    movl	%edi, -12(%rbp)
    vmovss	-8(%rbp), %xmm0
    vucomiss	-4(%rbp), %xmm0
    setb	%al
    xorl	$1, %eax
    testb	%al, %al
    je	L54
    cmpl	$0, -12(%rbp)
    jne	L56
    call	abort
L54:
    cmpl	$0, -12(%rbp)
    je	L56
    call	abort
L56:
    nop
    leave
    ret
    .globl	test_isgreater
test_isgreater:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    movl	%edi, -12(%rbp)
    vmovss	-4(%rbp), %xmm0
    vucomiss	-8(%rbp), %xmm0
    setbe	%al
    xorl	$1, %eax
    testb	%al, %al
    je	L58
    cmpl	$0, -12(%rbp)
    jne	L60
    call	abort
L58:
    cmpl	$0, -12(%rbp)
    je	L60
    call	abort
L60:
    nop
    leave
    ret
    .globl	test_isgreaterequal
test_isgreaterequal:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    movl	%edi, -12(%rbp)
    vmovss	-4(%rbp), %xmm0
    vucomiss	-8(%rbp), %xmm0
    setb	%al
    xorl	$1, %eax
    testb	%al, %al
    je	L62
    cmpl	$0, -12(%rbp)
    jne	L64
    call	abort
L62:
    cmpl	$0, -12(%rbp)
    je	L64
    call	abort
L64:
    nop
    leave
    ret
    .globl	test_islessgreater
test_islessgreater:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    movl	%edi, -12(%rbp)
    vmovss	-4(%rbp), %xmm0
    vucomiss	-8(%rbp), %xmm0
    sete	%al
    xorl	$1, %eax
    testb	%al, %al
    je	L66
    cmpl	$0, -12(%rbp)
    jne	L68
    call	abort
L66:
    cmpl	$0, -12(%rbp)
    je	L68
    call	abort
L68:
    nop
    leave
    ret
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movl	$6, -4(%rbp)
    movl	$0, -8(%rbp)
    jmp	L70
L71:
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movzbl	8(%rax), %eax
    andl	$1, %eax
    movzbl	%al, %ecx
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452 + 4, %rax
    vmovss	(%rax), %xmm0
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movl	(%rax), %eax
    movl	%ecx, %edi
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	test_isunordered
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movzbl	8(%rax), %eax
    shrb	%al
    andl	$1, %eax
    movzbl	%al, %ecx
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452 + 4, %rax
    vmovss	(%rax), %xmm0
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movl	(%rax), %eax
    movl	%ecx, %edi
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	test_isless
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movzbl	8(%rax), %eax
    shrb	$2, %al
    andl	$1, %eax
    movzbl	%al, %ecx
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452 + 4, %rax
    vmovss	(%rax), %xmm0
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movl	(%rax), %eax
    movl	%ecx, %edi
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	test_islessequal
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movzbl	8(%rax), %eax
    shrb	$3, %al
    andl	$1, %eax
    movzbl	%al, %ecx
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452 + 4, %rax
    vmovss	(%rax), %xmm0
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movl	(%rax), %eax
    movl	%ecx, %edi
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	test_isgreater
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movzbl	8(%rax), %eax
    shrb	$4, %al
    andl	$1, %eax
    movzbl	%al, %ecx
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452 + 4, %rax
    vmovss	(%rax), %xmm0
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movl	(%rax), %eax
    movl	%ecx, %edi
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	test_isgreaterequal
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movzbl	8(%rax), %eax
    shrb	$5, %al
    andl	$1, %eax
    movzbl	%al, %ecx
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452 + 4, %rax
    vmovss	(%rax), %xmm0
    movl	-8(%rbp), %eax
    movslq	%eax, %rdx
    movq	%rdx, %rax
    addq	%rax, %rax
    addq	%rdx, %rax
    salq	$2, %rax
    addq	$data2452, %rax
    movl	(%rax), %eax
    movl	%ecx, %edi
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	test_islessgreater
    addl	$1, -8(%rbp)
L70:
    movl	-8(%rbp), %eax
    cmpl	-4(%rbp), %eax
    jl	L71
    movl	$0, %edi
    call	exit
    .section	.rodata
data2452:
    .long	2143289344
    .long	2143289344
    .byte	1
    .zero	3
    .long	0
    .long	2143289344
    .byte	1
    .zero	3
    .long	2143289344
    .long	0
    .byte	1
    .zero	3
    .long	0
    .long	0
    .byte	20
    .zero	3
    .long	1065353216
    .long	1073741824
    .byte	38
    .zero	3
    .long	1073741824
    .long	1065353216
    .byte	56
    .zero	3
