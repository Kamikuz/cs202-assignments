
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $32, %rsp
  jmp start
start:
  movq $1, -8(%rbp)
  addq $2, -8(%rbp)
  movq -8(%rbp), %rax
  movq %rax, -16(%rbp)
  addq $3, -16(%rbp)
  movq $5, -24(%rbp)
  movq -16(%rbp), %rax
  movq %rax, -32(%rbp)
  movq -24(%rbp), %rax
  addq %rax, -32(%rbp)
  movq -32(%rbp), %rdi
  callq print_int
  jmp conclusion
conclusion:
  movq $0, %rax
  addq $32, %rsp
  popq %rbp
  retq
