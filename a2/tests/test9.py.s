
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $32, %rsp
  jmp start
start:
  movq $5, -8(%rbp)
  movq -8(%rbp), %rax
  movq %rax, -16(%rbp)
  movq -16(%rbp), %rax
  movq %rax, -8(%rbp)
  movq $10, -16(%rbp)
  movq -16(%rbp), %rax
  movq %rax, -24(%rbp)
  movq -8(%rbp), %rax
  addq %rax, -24(%rbp)
  movq -24(%rbp), %rdi
  callq print_int
  jmp conclusion
conclusion:
  movq $0, %rax
  addq $32, %rsp
  popq %rbp
  retq
