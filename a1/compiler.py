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
        case Module([Expr(Call(Name('print'), [Constant(number)]))]):
            return x86.Program({
                'start':
                    [
                        x86.NamedInstr(
                            "movq",
                            [
                                x86.Immediate(number),
                                x86.Reg("rdi")
                            ]),
                        x86.Callq("print_int"),
                        x86.Jmp("conclusion")
                    ]
            })


##################################################
# print-x86
##################################################

def print_x86(program: x86.Program) -> str:
    """
  Prints an x86 program to a string.
  :param program: An x86 program.
  :return: A string, ready for gcc.
  """
    
    def print_arg(arg: x86.Arg) -> str:
        match arg:
            case x86.Immediate(val):
                return f"${val}"
            case x86.Reg(val):
                return f"%{val}"
        pass
    
    def print_instr(instr: x86.Instr) -> str:
        match instr:
            case x86.NamedInstr(name, args):
                new_args = [print_arg(a) for a in args]
                out = f'{name} '
                out += ", ".join(new_args)
                return out
            case x86.Callq(label):
                return f"callq {label}"  # todo
            case x86.Jmp(label):
                return f"jmp {label}"
            case _:
                raise Exception('print_instr', instr)
    
    def print_program(program: x86.Program) -> str:
        match program:
            case x86.Program(blocks):
                labels = ""
                for label, instrs in blocks.items():
                    labels += label + ':'
                    for instr in instrs:
                        labels += '\n  ' + print_instr(instr)
                return labels
    
    out = """
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  jmp start\n"""
    out += print_program(program)
    out += """
conclusion:
  movq $0, %rax
  popq %rbp
  retq
"""
    return out


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
