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
    .globl	to_hex
to_hex:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$8, %rsp
    movl	%edi, -4(%rbp)
    cmpl	$15, -4(%rbp)
    jbe	L54
    call	abort
L54:
    movl	-4(%rbp), %eax
    movzbl	hex2437(%rax), %eax
    movsbl	%al, %eax
    leave
    ret
    .globl	fap
fap:
    pushq	%rbp
    movq	%rsp, %rbp
    pushq	%rbx
    subq	$88, %rsp
    movl	%edi, -68(%rbp)
    movq	%rsi, -80(%rbp)
    movq	%rdx, -88(%rbp)
    movq	$40, %rax
    movq	%rax, -24(%rbp)
    xorl	%eax, %eax
    leaq	-48(%rbp), %rax
    movq	-88(%rbp), %rdx
    movq	(%rdx), %rcx
    movq	%rcx, (%rax)
    movq	8(%rdx), %rcx
    movq	%rcx, 8(%rax)
    movq	16(%rdx), %rdx
    movq	%rdx, 16(%rax)
    movq	-80(%rbp), %rax
    movq	%rax, -56(%rbp)
    movq	-80(%rbp), %rax
    movq	%rax, %rdi
    call	strlen
    movq	%rax, %rdx
    movl	$16, %eax
    subl	-68(%rbp), %eax
    cltq
    cmpq	%rax, %rdx
    je	L58
    call	abort
L61:
    movq	-80(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -80(%rbp)
    movzbl	(%rax), %eax
    movsbl	%al, %ebx
    movq	-88(%rbp), %rax
    movl	(%rax), %eax
    cmpl	$48, %eax
    jnb	L59
    movq	-88(%rbp), %rax
    movq	16(%rax), %rdx
    movq	-88(%rbp), %rax
    movl	(%rax), %eax
    movl	%eax, %eax
    addq	%rdx, %rax
    movq	-88(%rbp), %rdx
    movl	(%rdx), %edx
    leal	8(%rdx), %ecx
    movq	-88(%rbp), %rdx
    movl	%ecx, (%rdx)
    jmp	L60
L59:
    movq	-88(%rbp), %rax
    movq	8(%rax), %rax
    leaq	8(%rax), %rcx
    movq	-88(%rbp), %rdx
    movq	%rcx, 8(%rdx)
L60:
    movl	(%rax), %eax
    movl	%eax, %edi
    call	to_hex
    cmpl	%eax, %ebx
    je	L58
    call	abort
L58:
    movq	-80(%rbp), %rax
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L61
    jmp	L62
L65:
    movq	-56(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -56(%rbp)
    movzbl	(%rax), %eax
    movsbl	%al, %ebx
    movl	-48(%rbp), %eax
    cmpl	$48, %eax
    jnb	L63
    movq	-32(%rbp), %rax
    movl	-48(%rbp), %edx
    movl	%edx, %edx
    addq	%rdx, %rax
    movl	-48(%rbp), %edx
    addl	$8, %edx
    movl	%edx, -48(%rbp)
    jmp	L64
L63:
    movq	-40(%rbp), %rax
    leaq	8(%rax), %rdx
    movq	%rdx, -40(%rbp)
L64:
    movl	(%rax), %eax
    movl	%eax, %edi
    call	to_hex
    cmpl	%eax, %ebx
    je	L62
    call	abort
L62:
    movq	-56(%rbp), %rax
    movzbl	(%rax), %eax
    testb	%al, %al
    jne	L65
    nop
    movq	-24(%rbp), %rax
    xorq	$40, %rax
    je	L66
    call	__stack_chk_fail
L66:
    addq	$88, %rsp
    popq	%rbx
    popq	%rbp
    ret
    .globl	f0
f0:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$224, %rsp
    movq	%rdi, -216(%rbp)
    movq	%rsi, -168(%rbp)
    movq	%rdx, -160(%rbp)
    movq	%rcx, -152(%rbp)
    movq	%r8, -144(%rbp)
    movq	%r9, -136(%rbp)
    testb	%al, %al
    je	L68
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L68:
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$8, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	16(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-216(%rbp), %rax
    movq	%rax, %rsi
    movl	$0, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L69
    call	__stack_chk_fail
L69:
    leave
    ret
    .globl	f1
f1:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$224, %rsp
    movl	%edi, -212(%rbp)
    movq	%rsi, -224(%rbp)
    movq	%rdx, -160(%rbp)
    movq	%rcx, -152(%rbp)
    movq	%r8, -144(%rbp)
    movq	%r9, -136(%rbp)
    testb	%al, %al
    je	L71
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L71:
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$16, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	16(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-224(%rbp), %rax
    movq	%rax, %rsi
    movl	$1, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L72
    call	__stack_chk_fail
L72:
    leave
    ret
    .globl	f2
f2:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$224, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movq	%rdx, -224(%rbp)
    movq	%rcx, -152(%rbp)
    movq	%r8, -144(%rbp)
    movq	%r9, -136(%rbp)
    testb	%al, %al
    je	L74
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L74:
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$24, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	16(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-224(%rbp), %rax
    movq	%rax, %rsi
    movl	$2, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L75
    call	__stack_chk_fail
L75:
    leave
    ret
    .globl	f3
f3:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movq	%rcx, -232(%rbp)
    movq	%r8, -144(%rbp)
    movq	%r9, -136(%rbp)
    testb	%al, %al
    je	L77
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L77:
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$32, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	16(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-232(%rbp), %rax
    movq	%rax, %rsi
    movl	$3, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L78
    call	__stack_chk_fail
L78:
    leave
    ret
    .globl	f4
f4:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movq	%r8, -232(%rbp)
    movq	%r9, -136(%rbp)
    testb	%al, %al
    je	L80
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L80:
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$40, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	16(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-232(%rbp), %rax
    movq	%rax, %rsi
    movl	$4, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L81
    call	__stack_chk_fail
L81:
    leave
    ret
    .globl	f5
f5:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movq	%r9, -240(%rbp)
    testb	%al, %al
    je	L83
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L83:
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	16(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$5, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L84
    call	__stack_chk_fail
L84:
    leave
    ret
    .globl	f6
f6:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L86
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L86:
    movq	16(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	24(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$6, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L87
    call	__stack_chk_fail
L87:
    leave
    ret
    .globl	f7
f7:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L89
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L89:
    movq	24(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	32(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$7, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L90
    call	__stack_chk_fail
L90:
    leave
    ret
    .globl	f8
f8:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L92
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L92:
    movq	32(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	40(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$8, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L93
    call	__stack_chk_fail
L93:
    leave
    ret
    .globl	f9
f9:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L95
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L95:
    movq	40(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	48(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$9, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L96
    call	__stack_chk_fail
L96:
    leave
    ret
    .globl	f10
f10:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L98
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L98:
    movq	48(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	56(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$10, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L99
    call	__stack_chk_fail
L99:
    leave
    ret
    .globl	f11
f11:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L101
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L101:
    movq	56(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	64(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$11, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L102
    call	__stack_chk_fail
L102:
    leave
    ret
    .globl	f12
f12:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L104
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L104:
    movq	64(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	72(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$12, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L105
    call	__stack_chk_fail
L105:
    leave
    ret
    .globl	f13
f13:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L107
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L107:
    movq	72(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	80(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$13, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L108
    call	__stack_chk_fail
L108:
    leave
    ret
    .globl	f14
f14:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L110
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L110:
    movq	80(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	88(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$14, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L111
    call	__stack_chk_fail
L111:
    leave
    ret
    .globl	f15
f15:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$240, %rsp
    movl	%edi, -212(%rbp)
    movl	%esi, -216(%rbp)
    movl	%edx, -220(%rbp)
    movl	%ecx, -224(%rbp)
    movl	%r8d, -228(%rbp)
    movl	%r9d, -232(%rbp)
    testb	%al, %al
    je	L113
    vmovaps	%xmm0, -128(%rbp)
    vmovaps	%xmm1, -112(%rbp)
    vmovaps	%xmm2, -96(%rbp)
    vmovaps	%xmm3, -80(%rbp)
    vmovaps	%xmm4, -64(%rbp)
    vmovaps	%xmm5, -48(%rbp)
    vmovaps	%xmm6, -32(%rbp)
    vmovaps	%xmm7, -16(%rbp)
L113:
    movq	88(%rbp), %rax
    movq	%rax, -240(%rbp)
    movq	$40, %rax
    movq	%rax, -184(%rbp)
    xorl	%eax, %eax
    movl	$48, -208(%rbp)
    movl	$48, -204(%rbp)
    leaq	96(%rbp), %rax
    movq	%rax, -200(%rbp)
    leaq	-176(%rbp), %rax
    movq	%rax, -192(%rbp)
    leaq	-208(%rbp), %rdx
    movq	-240(%rbp), %rax
    movq	%rax, %rsi
    movl	$15, %edi
    call	fap
    nop
    movq	-184(%rbp), %rax
    xorq	$40, %rax
    je	L114
    call	__stack_chk_fail
L114:
    leave
    ret
    .section	.rodata
LC0:
    .string	"0123456789abcdef"
    .text
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movq	$LC0, -8(%rbp)
    movq	-8(%rbp), %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	$5
    movl	$4, %r9d
    movl	$3, %r8d
    movl	$2, %ecx
    movl	$1, %edx
    movl	$0, %esi
    movq	%rax, %rdi
    movl	$0, %eax
    call	f0
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$1, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	$5
    movl	$4, %r9d
    movl	$3, %r8d
    movl	$2, %ecx
    movl	$1, %edx
    movq	%rax, %rsi
    movl	$0, %edi
    movl	$0, %eax
    call	f1
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$2, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	$5
    movl	$4, %r9d
    movl	$3, %r8d
    movl	$2, %ecx
    movq	%rax, %rdx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f2
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$3, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	$5
    movl	$4, %r9d
    movl	$3, %r8d
    movq	%rax, %rcx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f3
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$4, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	$5
    movl	$4, %r9d
    movq	%rax, %r8
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f4
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$5, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	$5
    movq	%rax, %r9
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f5
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$6, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    pushq	%rax
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f6
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$7, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	%rax
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f7
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$8, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	%rax
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f8
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$9, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	%rax
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f9
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$10, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	%rax
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f10
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$11, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	%rax
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f11
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$12, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	%rax
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f12
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$13, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	$13
    pushq	%rax
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f13
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$14, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	$14
    pushq	%rax
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f14
    addq	$96, %rsp
    movq	-8(%rbp), %rax
    addq	$15, %rax
    subq	$8, %rsp
    pushq	$15
    pushq	%rax
    pushq	$14
    pushq	$13
    pushq	$12
    pushq	$11
    pushq	$10
    pushq	$9
    pushq	$8
    pushq	$7
    pushq	$6
    movl	$5, %r9d
    movl	$4, %r8d
    movl	$3, %ecx
    movl	$2, %edx
    movl	$1, %esi
    movl	$0, %edi
    movl	$0, %eax
    call	f15
    addq	$96, %rsp
    movl	$0, %edi
    call	exit
    .data
hex2437:
    .string	"0123456789abcdef"
