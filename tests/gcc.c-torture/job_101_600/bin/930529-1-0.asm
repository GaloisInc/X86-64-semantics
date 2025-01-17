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
    .globl	dd
dd:
    pushq	%rbp
    movq	%rsp, %rbp
    movl	%edi, -4(%rbp)
    movl	%esi, -8(%rbp)
    movl	-4(%rbp), %eax
    cltd
    idivl	-8(%rbp)
    popq	%rbp
    ret
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movl	$-3, -4(%rbp)
    jmp	L44
L53:
    movl	-4(%rbp), %eax
    movl	$1, %esi
    movl	%eax, %edi
    call	dd
    cmpl	-4(%rbp), %eax
    je	L45
    call	abort
L45:
    movl	-4(%rbp), %eax
    movl	$2, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %ecx
    movl	-4(%rbp), %eax
    movl	%eax, %edx
    shrl	$31, %edx
    addl	%edx, %eax
    sarl	%eax
    cmpl	%eax, %ecx
    je	L46
    call	abort
L46:
    movl	-4(%rbp), %eax
    movl	$3, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$1431655766, %edx
    movl	%ecx, %eax
    imull	%edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L47
    call	abort
L47:
    movl	-4(%rbp), %eax
    movl	$4, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %ecx
    movl	-4(%rbp), %eax
    leal	3(%rax), %edx
    testl	%eax, %eax
    cmovs	%edx, %eax
    sarl	$2, %eax
    cmpl	%eax, %ecx
    je	L48
    call	abort
L48:
    movl	-4(%rbp), %eax
    movl	$5, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$1717986919, %edx
    movl	%ecx, %eax
    imull	%edx
    sarl	%edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L49
    call	abort
L49:
    movl	-4(%rbp), %eax
    movl	$6, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$715827883, %edx
    movl	%ecx, %eax
    imull	%edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L50
    call	abort
L50:
    movl	-4(%rbp), %eax
    movl	$7, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$-1840700269, %edx
    movl	%ecx, %eax
    imull	%edx
    leal	(%rdx,%rcx), %eax
    sarl	$2, %eax
    movl	%eax, %edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L51
    call	abort
L51:
    movl	-4(%rbp), %eax
    movl	$8, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %ecx
    movl	-4(%rbp), %eax
    leal	7(%rax), %edx
    testl	%eax, %eax
    cmovs	%edx, %eax
    sarl	$3, %eax
    cmpl	%eax, %ecx
    je	L52
    call	abort
L52:
    addl	$1, -4(%rbp)
L44:
    cmpl	$3, -4(%rbp)
    jle	L53
    movl	$2147483644, -4(%rbp)
    jmp	L54
L63:
    movl	-4(%rbp), %eax
    movl	$1, %esi
    movl	%eax, %edi
    call	dd
    cmpl	-4(%rbp), %eax
    je	L55
    call	abort
L55:
    movl	-4(%rbp), %eax
    movl	$2, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %ecx
    movl	-4(%rbp), %eax
    movl	%eax, %edx
    shrl	$31, %edx
    addl	%edx, %eax
    sarl	%eax
    cmpl	%eax, %ecx
    je	L56
    call	abort
L56:
    movl	-4(%rbp), %eax
    movl	$3, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$1431655766, %edx
    movl	%ecx, %eax
    imull	%edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L57
    call	abort
L57:
    movl	-4(%rbp), %eax
    movl	$4, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %ecx
    movl	-4(%rbp), %eax
    leal	3(%rax), %edx
    testl	%eax, %eax
    cmovs	%edx, %eax
    sarl	$2, %eax
    cmpl	%eax, %ecx
    je	L58
    call	abort
L58:
    movl	-4(%rbp), %eax
    movl	$5, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$1717986919, %edx
    movl	%ecx, %eax
    imull	%edx
    sarl	%edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L59
    call	abort
L59:
    movl	-4(%rbp), %eax
    movl	$6, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$715827883, %edx
    movl	%ecx, %eax
    imull	%edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L60
    call	abort
L60:
    movl	-4(%rbp), %eax
    movl	$7, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %esi
    movl	-4(%rbp), %ecx
    movl	$-1840700269, %edx
    movl	%ecx, %eax
    imull	%edx
    leal	(%rdx,%rcx), %eax
    sarl	$2, %eax
    movl	%eax, %edx
    movl	%ecx, %eax
    sarl	$31, %eax
    subl	%eax, %edx
    movl	%edx, %eax
    cmpl	%eax, %esi
    je	L61
    call	abort
L61:
    movl	-4(%rbp), %eax
    movl	$8, %esi
    movl	%eax, %edi
    call	dd
    movl	%eax, %ecx
    movl	-4(%rbp), %eax
    leal	7(%rax), %edx
    testl	%eax, %eax
    cmovs	%edx, %eax
    sarl	$3, %eax
    cmpl	%eax, %ecx
    je	L62
    call	abort
L62:
    addl	$1, -4(%rbp)
L54:
    movl	-4(%rbp), %eax
    cmpl	$-2147483646, %eax
    jbe	L63
    movl	$0, %edi
    call	exit
