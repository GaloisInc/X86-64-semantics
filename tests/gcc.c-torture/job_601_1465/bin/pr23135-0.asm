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
    .globl	i
    .data
i:
    .long	150
    .long	100
    .globl	j
j:
    .long	10
    .long	13
    .comm	k,8,8
    .comm	res,8,8
    .text
    .globl	verify
verify:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movl	%edi, -4(%rbp)
    movl	%esi, -8(%rbp)
    movl	%edx, -12(%rbp)
    movl	%ecx, -16(%rbp)
    movl	-4(%rbp), %eax
    cmpl	-12(%rbp), %eax
    jne	L54
    movl	-8(%rbp), %eax
    cmpl	-16(%rbp), %eax
    je	L56
L54:
    call	abort
L56:
    nop
    leave
    ret
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    pushq	%r12
    pushq	%rbx
    subq	$131520, %rsp
    movq	$40, %rax
    movq	%rax, -24(%rbp)
    xorl	%eax, %eax
    movq	i(%rip), %rdx
    movq	j(%rip), %rax
    movq	%rdx, -131176(%rbp)
    movl	-131176(%rbp), %esi
    movq	%rax, -131184(%rbp)
    movl	-131184(%rbp), %ecx
    addl	%esi, %ecx
    movq	%rdx, -131192(%rbp)
    movl	-131188(%rbp), %edx
    movq	%rax, -131200(%rbp)
    movl	-131196(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm1
    vpinsrd	$1, %eax, %xmm1, %xmm0
    vmovq	%xmm0, -131168(%rbp)
    movq	-131168(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$113, %ecx
    movl	$160, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rdx
    movq	j(%rip), %rax
    movq	%rdx, -131208(%rbp)
    movl	-131208(%rbp), %esi
    movq	%rax, -131216(%rbp)
    movl	-131216(%rbp), %ecx
    imull	%esi, %ecx
    movq	%rdx, -131224(%rbp)
    movl	-131220(%rbp), %edx
    movq	%rax, -131232(%rbp)
    movl	-131228(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm2
    vpinsrd	$1, %eax, %xmm2, %xmm0
    vmovq	%xmm0, -131160(%rbp)
    movq	-131160(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$1300, %ecx
    movl	$1500, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rsi
    movq	j(%rip), %rcx
    movq	%rsi, -131240(%rbp)
    movl	-131240(%rbp), %eax
    movq	%rcx, -131248(%rbp)
    movl	-131248(%rbp), %ebx
    cltd
    idivl	%ebx
    movl	%eax, %edi
    movq	%rsi, -131256(%rbp)
    movl	-131252(%rbp), %eax
    movq	%rcx, -131264(%rbp)
    movl	-131260(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%edi, %xmm3
    vpinsrd	$1, %eax, %xmm3, %xmm0
    vmovq	%xmm0, -131152(%rbp)
    movq	-131152(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$7, %ecx
    movl	$15, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rdx
    movq	j(%rip), %rax
    andq	%rdx, %rax
    movq	%rax, -131144(%rbp)
    movq	-131144(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$4, %ecx
    movl	$2, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rdx
    movq	j(%rip), %rax
    orq	%rdx, %rax
    movq	%rax, -131136(%rbp)
    movq	-131136(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$109, %ecx
    movl	$158, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rdx
    movq	j(%rip), %rax
    xorq	%rdx, %rax
    movq	%rax, -131128(%rbp)
    movq	-131128(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$105, %ecx
    movl	$156, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rax
    movq	%rax, -131272(%rbp)
    movl	-131272(%rbp), %edx
    negl	%edx
    movq	%rax, -131280(%rbp)
    movl	-131276(%rbp), %eax
    negl	%eax
    vmovd	%edx, %xmm4
    vpinsrd	$1, %eax, %xmm4, %xmm0
    vmovq	%xmm0, -131120(%rbp)
    movq	-131120(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$-100, %ecx
    movl	$-150, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movq	i(%rip), %rax
    notq	%rax
    movq	%rax, -131112(%rbp)
    movq	-131112(%rbp), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$-101, %ecx
    movl	$-151, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movl	-131168(%rbp), %edx
    movl	-131160(%rbp), %eax
    leal	(%rdx,%rax), %ecx
    movl	-131164(%rbp), %edx
    movl	-131156(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm5
    vpinsrd	$1, %eax, %xmm5, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131288(%rbp)
    movl	-131288(%rbp), %ecx
    movl	-131144(%rbp), %edx
    addl	%edx, %ecx
    movq	%rax, -131296(%rbp)
    movl	-131292(%rbp), %edx
    movl	-131140(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm6
    vpinsrd	$1, %eax, %xmm6, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131304(%rbp)
    movl	-131304(%rbp), %ecx
    movl	-131136(%rbp), %edx
    addl	%edx, %ecx
    movq	%rax, -131312(%rbp)
    movl	-131308(%rbp), %edx
    movl	-131132(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm7
    vpinsrd	$1, %eax, %xmm7, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131320(%rbp)
    movl	-131320(%rbp), %ecx
    movl	-131128(%rbp), %edx
    addl	%edx, %ecx
    movq	%rax, -131328(%rbp)
    movl	-131324(%rbp), %edx
    movl	-131124(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm1
    vpinsrd	$1, %eax, %xmm1, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131336(%rbp)
    movl	-131336(%rbp), %ecx
    movl	-131120(%rbp), %edx
    addl	%edx, %ecx
    movq	%rax, -131344(%rbp)
    movl	-131340(%rbp), %edx
    movl	-131116(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm2
    vpinsrd	$1, %eax, %xmm2, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131352(%rbp)
    movl	-131352(%rbp), %ecx
    movl	-131112(%rbp), %edx
    addl	%edx, %ecx
    movq	%rax, -131360(%rbp)
    movl	-131356(%rbp), %edx
    movl	-131108(%rbp), %eax
    addl	%edx, %eax
    vmovd	%ecx, %xmm3
    vpinsrd	$1, %eax, %xmm3, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, k(%rip)
    movq	k(%rip), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$1430, %ecx
    movl	$1675, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movl	-131168(%rbp), %edx
    movl	-131160(%rbp), %eax
    movl	%edx, %ecx
    imull	%eax, %ecx
    movl	-131164(%rbp), %edx
    movl	-131156(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm4
    vpinsrd	$1, %eax, %xmm4, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131368(%rbp)
    movl	-131368(%rbp), %ecx
    movl	-131144(%rbp), %edx
    imull	%edx, %ecx
    movq	%rax, -131376(%rbp)
    movl	-131372(%rbp), %edx
    movl	-131140(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm5
    vpinsrd	$1, %eax, %xmm5, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131384(%rbp)
    movl	-131384(%rbp), %ecx
    movl	-131136(%rbp), %edx
    imull	%edx, %ecx
    movq	%rax, -131392(%rbp)
    movl	-131388(%rbp), %edx
    movl	-131132(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm6
    vpinsrd	$1, %eax, %xmm6, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131400(%rbp)
    movl	-131400(%rbp), %ecx
    movl	-131128(%rbp), %edx
    imull	%edx, %ecx
    movq	%rax, -131408(%rbp)
    movl	-131404(%rbp), %edx
    movl	-131124(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm7
    vpinsrd	$1, %eax, %xmm7, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131416(%rbp)
    movl	-131416(%rbp), %ecx
    movl	-131120(%rbp), %edx
    imull	%edx, %ecx
    movq	%rax, -131424(%rbp)
    movl	-131420(%rbp), %edx
    movl	-131116(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm1
    vpinsrd	$1, %eax, %xmm1, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, -131432(%rbp)
    movl	-131432(%rbp), %ecx
    movl	-131112(%rbp), %edx
    imull	%edx, %ecx
    movq	%rax, -131440(%rbp)
    movl	-131436(%rbp), %edx
    movl	-131108(%rbp), %eax
    imull	%edx, %eax
    vmovd	%ecx, %xmm2
    vpinsrd	$1, %eax, %xmm2, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, k(%rip)
    movq	k(%rip), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$-1579586240, %ecx
    movl	$1456467968, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movl	-131168(%rbp), %eax
    movl	-131160(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movl	-131164(%rbp), %eax
    movl	-131156(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm3
    vpinsrd	$1, %eax, %xmm3, %xmm0
    vmovq	%xmm0, %rcx
    movq	%rcx, -131448(%rbp)
    movl	-131448(%rbp), %eax
    movl	-131152(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movq	%rcx, -131456(%rbp)
    movl	-131452(%rbp), %eax
    movl	-131148(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm4
    vpinsrd	$1, %eax, %xmm4, %xmm0
    vmovq	%xmm0, %rcx
    movq	%rcx, -131464(%rbp)
    movl	-131464(%rbp), %eax
    movl	-131144(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movq	%rcx, -131472(%rbp)
    movl	-131468(%rbp), %eax
    movl	-131140(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm5
    vpinsrd	$1, %eax, %xmm5, %xmm0
    vmovq	%xmm0, %rcx
    movq	%rcx, -131480(%rbp)
    movl	-131480(%rbp), %eax
    movl	-131136(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movq	%rcx, -131488(%rbp)
    movl	-131484(%rbp), %eax
    movl	-131132(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm6
    vpinsrd	$1, %eax, %xmm6, %xmm0
    vmovq	%xmm0, %rcx
    movq	%rcx, -131496(%rbp)
    movl	-131496(%rbp), %eax
    movl	-131128(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movq	%rcx, -131504(%rbp)
    movl	-131500(%rbp), %eax
    movl	-131124(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm7
    vpinsrd	$1, %eax, %xmm7, %xmm0
    vmovq	%xmm0, %rcx
    movq	%rcx, -131512(%rbp)
    movl	-131512(%rbp), %eax
    movl	-131120(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movq	%rcx, -131520(%rbp)
    movl	-131516(%rbp), %eax
    movl	-131116(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm1
    vpinsrd	$1, %eax, %xmm1, %xmm0
    vmovq	%xmm0, %rcx
    movq	%rcx, -131528(%rbp)
    movl	-131528(%rbp), %eax
    movl	-131112(%rbp), %edi
    cltd
    idivl	%edi
    movl	%eax, %esi
    movq	%rcx, -131536(%rbp)
    movl	-131532(%rbp), %eax
    movl	-131108(%rbp), %ebx
    cltd
    idivl	%ebx
    vmovd	%esi, %xmm2
    vpinsrd	$1, %eax, %xmm2, %xmm0
    vmovq	%xmm0, %rax
    movq	%rax, k(%rip)
    movq	k(%rip), %rax
    movq	%rax, res(%rip)
    movl	res + 4(%rip), %r12d
    movl	res(%rip), %ebx
    subq	$131072, %rsp
    movq	%rsp, %rax
    movq	%rax, %rcx
    leaq	-131104(%rbp), %rax
    movl	$131072, %edx
    movq	%rax, %rsi
    movq	%rcx, %rdi
    call	memcpy
    movl	$0, %ecx
    movl	$0, %edx
    movl	%r12d, %esi
    movl	%ebx, %edi
    call	verify
    addq	$131072, %rsp
    movl	$0, %edi
    call	exit
