
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  jmp start
start:
  movq $34, -8(%rbp)
  addq $3, -8(%rbp)
  movq -8(%rbp), %rax
  movq %rax, -16(%rbp)
  addq $5, -16(%rbp)
  movq -16(%rbp), %rdi
  callq print_int
  jmp conclusion
conclusion:
  movq $0, %rax
  addq $16, %rsp
  popq %rbp
  retq
