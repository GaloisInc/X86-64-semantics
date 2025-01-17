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
    jle	L37
    cmpl	$122, -4(%rbp)
    jg	L37
    movl	$1, %eax
    jmp	L38
L37:
    cmpl	$64, -4(%rbp)
    jle	L39
    cmpl	$90, -4(%rbp)
    jg	L39
    movl	$1, %eax
    jmp	L38
L39:
    cmpl	$47, -4(%rbp)
    jle	L40
    cmpl	$57, -4(%rbp)
    jg	L40
    movl	$1, %eax
    jmp	L38
L40:
    movl	$0, %eax
L38:
    popq	%rbp
    ret
    .globl	w
w:
    pushq	%rbp
    movq	%rsp, %rbp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    nop
    popq	%rbp
    ret
    .globl	f1
f1:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$8, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    vxorps	%xmm0, %xmm0, %xmm0
    vucomiss	-4(%rbp), %xmm0
    jp	L43
    vxorps	%xmm0, %xmm0, %xmm0
    vucomiss	-4(%rbp), %xmm0
    jne	L43
    vxorps	%xmm0, %xmm0, %xmm0
    vucomiss	-8(%rbp), %xmm0
    jp	L43
    vxorps	%xmm0, %xmm0, %xmm0
    vucomiss	-8(%rbp), %xmm0
    je	L46
L43:
    call	abort
L46:
    nop
    leave
    ret
    .globl	f2
f2:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$8, %rsp
    vmovss	%xmm0, -4(%rbp)
    vmovss	%xmm1, -8(%rbp)
    vmovss	LC1(%rip), %xmm0
    vucomiss	-4(%rbp), %xmm0
    jp	L48
    vmovss	LC1(%rip), %xmm0
    vucomiss	-4(%rbp), %xmm0
    jne	L48
    vmovss	LC1(%rip), %xmm0
    vucomiss	-8(%rbp), %xmm0
    jp	L48
    vmovss	LC1(%rip), %xmm0
    vucomiss	-8(%rbp), %xmm0
    je	L51
L48:
    call	abort
L51:
    nop
    leave
    ret
    .globl	gitter
gitter:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$65616, %rsp
    movl	%edi, -65572(%rbp)
    movq	%rsi, -65584(%rbp)
    movq	%rdx, -65592(%rbp)
    movq	%rcx, -65600(%rbp)
    movq	%r8, -65608(%rbp)
    vmovss	%xmm0, -65576(%rbp)
    movq	$40, %rax
    movq	%rax, -8(%rbp)
    xorl	%eax, %eax
    movq	-65608(%rbp), %rax
    vmovss	4(%rax), %xmm0
    movq	-65608(%rbp), %rax
    movl	(%rax), %eax
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	f1
    movq	-65608(%rbp), %rax
    addq	$8, %rax
    vmovss	4(%rax), %xmm0
    movq	-65608(%rbp), %rax
    addq	$8, %rax
    movl	(%rax), %eax
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	f2
    movq	-65600(%rbp), %rax
    movl	$0, (%rax)
    movq	-65584(%rbp), %rax
    vmovss	(%rax), %xmm0
    vmovss	%xmm0, -65556(%rbp)
    vxorps	%xmm0, %xmm0, %xmm0
    vucomiss	-65556(%rbp), %xmm0
    jb	L53
    vmovss	-65576(%rbp), %xmm0
    movl	-65556(%rbp), %eax
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	w
    vcvtss2sd	-65556(%rbp), %xmm1, %xmm1
    vcvtss2sd	-65576(%rbp), %xmm0, %xmm0
    vmovsd	LC2(%rip), %xmm2
    vmulsd	%xmm2, %xmm0, %xmm0
    vucomisd	%xmm1, %xmm0
    jb	L53
    vmovss	-65576(%rbp), %xmm0
    movl	-65556(%rbp), %eax
    vmovaps	%xmm0, %xmm1
    vmovd	%eax, %xmm0
    call	w
    movq	-65592(%rbp), %rax
    vmovss	LC1(%rip), %xmm0
    vmovss	%xmm0, (%rax)
L53:
    nop
    movq	-8(%rbp), %rdx
    xorq	$40, %rdx
    je	L56
    call	__stack_chk_fail
L56:
    leave
    ret
    .globl	pos
    .bss
pos:
    .zero	8
    .globl	limit
    .data
limit:
    .long	0
    .long	0
    .long	1065353216
    .long	1065353216
    .text
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movq	$40, %rax
    movq	%rax, -8(%rbp)
    xorl	%eax, %eax
    leaq	-12(%rbp), %rdx
    leaq	-16(%rbp), %rax
    vmovss	LC1(%rip), %xmm0
    movl	$limit, %r8d
    movq	%rdx, %rcx
    movq	%rax, %rdx
    movl	$pos, %esi
    movl	$1, %edi
    call	gitter
    movl	$0, %edi
    call	exit
    .section	.rodata
LC1:
    .long	1065353216
LC2:
    .long	0
    .long	1071644672
