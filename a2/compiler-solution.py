from ast import *

from typing import List, Set, Dict, Tuple
import sys
import traceback

from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86

gensym_num = 0


def gensym(x):
    """
    Constructs a new variable name guaranteed to be unique.
    :param x: A "base" variable name (e.g. "x")
    :return: A unique variable name (e.g. "x_1")
    """

    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


##################################################
# remove-complex-opera*
##################################################

def rco(prog: Module) -> Module:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lvar program
    :return: An Lvar program with atomic operator arguments.
    """

    def rco_stmts(stmts: List[stmt]) -> List[stmt]:
        new_stmts = []

        for stmt in stmts:
            bindings = {}

            match stmt:
                case Assign([x], e1):
                    new_e1 = rco_exp(e1, False, bindings)
                    new_stmt = Assign([x], new_e1)
                case Expr(Call(Name('print'), [e1])):
                    new_e1 = rco_exp(e1, True, bindings)
                    new_stmt = Expr(Call(Name('print'), [new_e1]))
                case _:
                    raise Exception('rco_stmt', stmt)

            # (1) add the new bindings created by rco_exp
            new_stmts.extend([Assign([x], e) for x, e in bindings.items()])
            # (2) add the compiled statement itself
            new_stmts.append(new_stmt)

        return new_stmts

    def rco_exp(e: expr, atomic: bool, bindings: Dict[str, expr]) -> expr:
        match e:
            case Name(x):
                return Name(x)
            case Constant(i):
                return Constant(i)
            case BinOp(e1, op, e2):
                new_e1 = rco_exp(e1, True, bindings)
                new_e2 = rco_exp(e2, True, bindings)
                new_e = BinOp(new_e1, op, new_e2)

                if atomic:
                    new_v = Name(gensym('tmp'))
                    bindings[new_v] = new_e
                    return new_v
                else:
                    return new_e
            case _:
                raise Exception('rco_exp', e)

    return Module(rco_stmts(prog.body))


##################################################
# select-instructions
##################################################

def select_instructions(prog: Module) -> x86.Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """

    def si_stmts(stmts: List[stmt]) -> List[x86.Instr]:
        instrs = []

        for stmt in stmts:
            match stmt:
                case Assign([x], BinOp(e1, Add(), e2)):
                    instrs.append(x86.NamedInstr('movq', [si_atm(e1), si_atm(x)]))
                    instrs.append(x86.NamedInstr('addq', [si_atm(e2), si_atm(x)]))
                case Assign([x], Constant(i)):
                    instrs.append(x86.NamedInstr('movq', [x86.Immediate(i), si_atm(x)]))
                case Assign([x], y):
                    instrs.append(x86.NamedInstr('movq', [si_atm(y), si_atm(x)]))
                case Expr(Call(Name('print'), [e1])):
                    instrs.append(x86.NamedInstr('movq', [si_atm(e1), x86.Reg('rdi')]))
                    instrs.append(x86.Callq('print_int'))
                case _:
                    raise Exception('si_stmts', stmt)

        return instrs

    def si_atm(a: expr) -> x86.Arg:
        match a:
            case Constant(i):
                return x86.Immediate(i)
            case Name(x):
                return x86.Var(x)
            case _:
                raise Exception('si_atm', a)

    instrs: List[x86.Instr] = si_stmts(prog.body) + [x86.Jmp('conclusion')]
    return x86.Program({'start': instrs})


##################################################
# assign-homes
##################################################

def assign_homes(program: x86.Program) -> Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocates a stack location for each
    variable in the program.
    :param program: An x86 program.
    :return: A Tuple. The first element is an x86 program (with no variable references).
    The second element is the number of bytes needed in stack locations.
    """

    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))

    homes = {}

    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(i):
                return a
            case x86.Reg(r):
                return a
            case x86.Var(x):
                if x in homes:
                    return homes[x]
                else:
                    current_stack_size = len(homes) * 8
                    new_stack_size = - (current_stack_size + 8)
                    homes[x] = x86.Deref('rbp', new_stack_size)
                    return x86.Deref('rbp', new_stack_size)
            case _:
                raise Exception('ah_arg', a)

    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(i, args):
                return x86.NamedInstr(i, [ah_arg(a) for a in args])
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp)):
                    return e
                else:
                    raise Exception('ah_instr', e)

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]

    blocks = program.blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}
    return x86.Program(new_blocks), align(8 * len(homes))


##################################################
# patch-instructions
##################################################

def patch_instructions(inputs: Tuple[x86.Program, int]) -> Tuple[x86.Program, int]:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param inputs: A Tuple. The first element is an x86 program. The second element is the
    stack space in bytes.
    :return: A Tuple. The first element is the patched x86 program. The second element is
    the stack space in bytes.
    """

    def pi_instr(e: x86.Instr) -> List[x86.Instr]:
        match e:
            case x86.NamedInstr('movq', [x86.Deref(_, _), x86.Deref(_, _)]):
                return [x86.NamedInstr('movq', [e.args[0], x86.Reg('rax')]),
                        x86.NamedInstr('movq', [x86.Reg('rax'), e.args[1]])]
            case x86.NamedInstr('addq', [x86.Deref(_, _), x86.Deref(_, _)]):
                return [x86.NamedInstr('movq', [e.args[0], x86.Reg('rax')]),
                        x86.NamedInstr('addq', [x86.Reg('rax'), e.args[1]])]
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.NamedInstr)):
                    return [e]
                else:
                    raise Exception('pi_instr', e)

    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instrs = [pi_instr(i) for i in instrs]
        flattened = [val for sublist in new_instrs for val in sublist]
        return flattened

    program, stack_size = inputs
    blocks = program.blocks
    new_blocks = {label: pi_block(block) for label, block in blocks.items()}
    return (x86.Program(new_blocks), stack_size)


##################################################
# print-x86
##################################################

def print_x86(inputs: Tuple[x86.Program, int]) -> str:
    """
    Prints an x86 program to a string.
    :param inputs: A Tuple. The first element is the x86 program. The second element
    is the stack space in bytes.
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
            case x86.Deref(register, offset):
                return f'{offset}(%{register})'
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

    program, stack_size = inputs
    blocks = program.blocks
    block_instrs = '\n'.join([print_block(label, block) for label, block in blocks.items()])

    program = f"""
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq ${stack_size}, %rsp
  jmp start
{block_instrs}
conclusion:
  movq $0, %rax
  addq ${stack_size}, %rsp
  popq %rbp
  retq
"""

    return program


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'remove complex opera*': rco,
    'select instructions': select_instructions,
    'assign homes': assign_homes,
    'patch instructions': patch_instructions,
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
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())
