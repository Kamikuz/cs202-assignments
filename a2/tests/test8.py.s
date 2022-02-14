
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  jmp start
start:
  movq $5, -8(%rbp)
  addq $10, -8(%rbp)
  movq -8(%rbp), %rax
  movq %rax, -8(%rbp)
  addq $10, -8(%rbp)
  movq -8(%rbp), %rdi
  callq print_int
  jmp conclusion
conclusion:
  movq $0, %rax
  addq $16, %rsp
  popq %rbp
  retq
