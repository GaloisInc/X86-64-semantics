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
    .comm	poolptr,8,8
    .comm	strpool,8,8
    .section	.rodata
LC0:
    .string	"mu"
LC1:
    .string	""
LC2:
    .string	"x"
LC3:
    .string	"xx"
LC4:
    .string	"xxx"
    .data
poolfilearr:
    .quad	LC0
    .quad	LC1
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC3
    .quad	LC2
    .quad	LC2
    .quad	LC4
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	LC2
    .quad	0
    .text
    .globl	makestring
makestring:
    pushq	%rbp
    movq	%rsp, %rbp
    movl	$1, %eax
    popq	%rbp
    ret
    .globl	loadpoolstrings
loadpoolstrings:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$40, %rsp
    movq	%rdi, -40(%rbp)
    movq	$0, -8(%rbp)
    movl	$0, -28(%rbp)
    movl	$0, -24(%rbp)
    jmp	L56
L61:
    movq	-16(%rbp), %rax
    movq	$-1, %rcx
    movq	%rax, %rdx
    movl	$0, %eax
    movq	%rdx, %rdi
    repnz scasb
    movq	%rcx, %rax
    notq	%rax
    subq	$1, %rax
    movl	%eax, -20(%rbp)
    movl	-20(%rbp), %eax
    addl	%eax, -28(%rbp)
    movl	-28(%rbp), %eax
    cltq
    cmpq	-40(%rbp), %rax
    jl	L59
    movl	$0, %eax
    jmp	L58
L60:
    movq	strpool(%rip), %rcx
    movq	poolptr(%rip), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, poolptr(%rip)
    addq	%rax, %rcx
    movq	-16(%rbp), %rax
    leaq	1(%rax), %rdx
    movq	%rdx, -16(%rbp)
    movzbl	(%rax), %eax
    movb	%al, (%rcx)
L59:
    movl	-20(%rbp), %eax
    leal	-1(%rax), %edx
    movl	%edx, -20(%rbp)
    testl	%eax, %eax
    jg	L60
    call	makestring
    movq	%rax, -8(%rbp)
L56:
    movl	-24(%rbp), %eax
    leal	1(%rax), %edx
    movl	%edx, -24(%rbp)
    cltq
    movq	poolfilearr(,%rax,8), %rax
    movq	%rax, -16(%rbp)
    cmpq	$0, -16(%rbp)
    jne	L61
    movq	-8(%rbp), %rax
L58:
    leave
    ret
    .globl	main
.globl _start
_start:
    pushq	%rbp
    movq	%rsp, %rbp
    subq	$16, %rsp
    movl	$4000, %edi
    call	malloc
    movq	%rax, strpool(%rip)
    movq	strpool(%rip), %rax
    testq	%rax, %rax
    jne	L63
    movl	$0, %eax
    jmp	L64
L63:
    movl	$4000, %edi
    call	loadpoolstrings
    movl	%eax, -4(%rbp)
    movq	strpool(%rip), %rax
    movq	%rax, %rdi
    call	free
    movl	$0, %eax
L64:
    leave
    ret
