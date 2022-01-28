
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  jmp start
start:
  movq $873, %rdi
  callq print_int
  jmp conclusion
conclusion:
  movq $0, %rax
  popq %rbp
  retq
