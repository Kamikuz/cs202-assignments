from ast import *
from typing import List, Set, Dict, Tuple
import sys

from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86


##################################################
# select-instructions
##################################################

def select_instructions(program: Module) -> x86.Program:
    """
    Transforms a Lmin program into a pseudo-x86 assembly program.
    :param program: a Lmin program
    :return: a pseudo-x86 program
    """

    match program:
        case Module([Expr(Call(Name("print"), [Constant(i)]))]):
            instrs = [
                x86.NamedInstr('movq', [x86.Immediate(i), x86.Reg('rdi')]),
                x86.Callq('print_int'),
                x86.Jmp('conclusion')
            ]
            return x86.Program({'start': instrs})
        case _:
            raise Exception('select_instructions', program)


##################################################
# print-x86
##################################################

def print_x86(program: x86.Program) -> str:
    """
    Prints an x86 program to a string.
    :param program: An x86 program.
    :return: A string, ready for gcc.
    """

    def print_arg(a: x86.Arg) -> str:
        match a:
            case x86.Immediate(i):
                return f'${i}'
            case x86.Reg(r):
                return f'%{r}'
            case x86.Var(x):
                return f'#{x}'
            case x86.Deref(offset, val):
                return f'{offset}(%{val})'
            case _:
                raise Exception('print_arg', a)

    def print_instr(e: x86.Instr) -> str:
        match e:
            case x86.NamedInstr(name, args):
                arg_str = ', '.join([print_arg(a) for a in args])
                return f'{name} {arg_str}'
            case x86.Callq(label):
                return f'callq {label}'
            case x86.Retq:
                return f'retq'
            case x86.Jmp(label):
                return f'jmp {label}'
            case _:
                raise Exception('print_instr', e)

    def print_block(label: str, instrs: List[x86.Instr]) -> str:
        name = f'{label}:\n'
        instr_strs = '\n'.join(['  ' + print_instr(i) for i in instrs])
        return name + instr_strs

    blocks = program.blocks
    block_instrs = '\n'.join([print_block(label, block) for label, block in blocks.items()])

    output = f"""
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  jmp start
{block_instrs}
conclusion:
  movq $0, %rax
  popq %rbp
  retq
"""

    return output


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'select instructions': select_instructions,
    'print x86': print_x86
}


def run_compiler(s, logging=False):
    current_program = parse(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print(print_ast(current_program))

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print(print_ast(current_program))

    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                input_program = f.read()
                x86_program = run_compiler(input_program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except Exception as e:
                raise Exception('Error during compilation:', e)
