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
nested2410:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$32, %rsp
    movq	%r10, %rax
    movq	%r10, -24(%rbp)
    movq	$40, %rcx
    movq	%rcx, -8(%rbp)
    xorl	%ecx, %ecx
    movl	$254, %edx
    movl	%edx, (%rax)
    nop
    movq	-8(%rbp), %rax
    xorq	$40, %rax
    je	L42
    call	__stack_chk_fail
L42:
    leave
    ret
    .globl	foo
foo:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movq	$40, %rax
    movq	%rax, -8(%rbp)
    xorl	%eax, %eax
    movl	$0, %eax
    movl	%eax, -16(%rbp)
    leaq	-16(%rbp), %rax
    movq	%rax, %r10
    call	nested2410
    movl	-16(%rbp), %eax
    movl	-16(%rbp), %eax
    movl	-16(%rbp), %eax
    movl	%eax, -16(%rbp)
    movl	-16(%rbp), %eax
    movq	-8(%rbp), %rdx
    xorq	$40, %rdx
    je	L45
    call	__stack_chk_fail
L45:
    leave
    ret
nested2417:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$32, %rsp
    movq	%r10, %rax
    movq	%r10, -24(%rbp)
    movq	$40, %rcx
    movq	%rcx, -8(%rbp)
    xorl	%ecx, %ecx
    movl	(%rax), %edx
    movl	(%rax), %edx
    movl	(%rax), %edx
    addl	$4, %edx
    movl	%edx, (%rax)
    movl	(%rax), %edx
    movl	%edx, (%rax)
    nop
    movq	-8(%rbp), %rax
    xorq	$40, %rax
    je	L47
    call	__stack_chk_fail
L47:
    leave
    ret
    .globl	bar
bar:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movq	$40, %rax
    movq	%rax, -8(%rbp)
    xorl	%eax, %eax
    movl	$0, %eax
    movl	%eax, -16(%rbp)
    leaq	-16(%rbp), %rax
    movq	%rax, %r10
    call	nested2417
    movl	-16(%rbp), %eax
    movq	-8(%rbp), %rdx
    xorq	$40, %rdx
    je	L50
    call	__stack_chk_fail
L50:
    leave
    ret
nested22427:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$32, %rsp
    movq	%r10, %rax
    movq	%r10, -24(%rbp)
    movq	$40, %rsi
    movq	%rsi, -8(%rbp)
    xorl	%esi, %esi
    movq	(%rax), %rdx
    movl	(%rdx), %edx
    movq	(%rax), %rdx
    movq	(%rax), %rdx
    movl	(%rdx), %edx
    movq	(%rax), %rdx
    movl	(%rdx), %edx
    leal	4(%rdx), %ecx
    movq	(%rax), %rdx
    movl	%ecx, (%rdx)
    movq	(%rax), %rdx
    movl	(%rdx), %edx
    movq	(%rax), %rcx
    movl	%edx, (%rcx)
    movq	(%rax), %rdx
    movq	(%rax), %rax
    nop
    movq	-8(%rbp), %rax
    xorq	$40, %rax
    je	L52
    call	__stack_chk_fail
L52:
    leave
    ret
nested2424:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$32, %rsp
    movq	%r10, %rax
    movq	%r10, -24(%rbp)
    movq	$40, %rdx
    movq	%rdx, -8(%rbp)
    xorl	%edx, %edx
    movq	%rax, -16(%rbp)
    leaq	-16(%rbp), %rax
    movq	%rax, %r10
    call	nested22427
    leaq	-16(%rbp), %rax
    movq	%rax, %r10
    call	nested22427
    nop
    movq	-8(%rbp), %rax
    xorq	$40, %rax
    je	L54
    call	__stack_chk_fail
L54:
    leave
    ret
    .globl	baz
baz:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movq	$40, %rax
    movq	%rax, -8(%rbp)
    xorl	%eax, %eax
    movl	$0, %eax
    movl	%eax, -16(%rbp)
    leaq	-16(%rbp), %rax
    movq	%rax, %r10
    call	nested2424
    movl	-16(%rbp), %eax
    movq	-8(%rbp), %rdx
    xorq	$40, %rdx
    je	L57
    call	__stack_chk_fail
L57:
    leave
    ret
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    call	foo
    cmpl	$254, %eax
    jne	L59
    call	bar
    cmpl	$4, %eax
    jne	L59
    call	baz
    cmpl	$8, %eax
    je	L60
L59:
    call	abort
L60:
    movl	$0, %eax
    popq	%rbp
    ret
