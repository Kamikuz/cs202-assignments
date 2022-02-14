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
        new_statements = []
        
        for s in stmts:
            bindings = {}
            match s:
                case Assign([Name(var)], exp):
                    s = rco_exp(exp, bindings, False)
                    for (name, _exp) in bindings.items():
                        new_statements.append(Assign([name], _exp))
                    new_statements.append(Assign([Name(var, Store())], s))
                case Expr(Call(Name('print'), [exp])):
                    s = rco_exp(exp, bindings, True)
                    for (name, _exp) in bindings.items():
                        new_statements.append(Assign([name], _exp))
                    new_statements.append(Expr(Call(Name('print'), [s])))
        return new_statements
    
    def rco_exp(e: expr, bindings: Dict[str, expr], atomic: bool) -> expr:
        match e:
            case Constant(i):
                return Constant(i)
            case Name(var):
                return Name(var)
            case BinOp(e1, Add(), e2):
                new_e1 = rco_exp(e1, bindings, True)
                new_e2 = rco_exp(e2, bindings, True)
                if atomic:
                    tmp = Name(gensym('tmp'))
                    bindings[tmp] = BinOp(new_e1, Add(), new_e2)
                    return tmp
                else:
                    return BinOp(new_e1, Add(), new_e2)
    
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
    
    def si_arg(e: expr) -> x86.Arg:
        match e:
            case Constant(i):
                return x86.Immediate(i)
            case Name(var):
                return x86.Var(var)
    
    def si_stmts(statements: List[stmt]) -> List[x86.Instr]:
        new_instrs = []
        for s in statements:
            match s:
                case Assign([name], BinOp(a1, Add(), a2)):
                    new_instrs.append(x86.NamedInstr('movq', [si_arg(a1), si_arg(name)]))
                    new_instrs.append(x86.NamedInstr('addq', [si_arg(a2), si_arg(name)]))
                case Assign([name], exp):
                    new_instrs.append(x86.NamedInstr('movq', [si_arg(exp), si_arg(name)]))
                case Expr(Call(Name('print'), [a1])):
                    new_instrs.append(x86.NamedInstr('movq', [si_arg(a1), x86.Reg('rdi')]))
                    new_instrs.append(x86.Callq('print_int'), )
        
        new_instrs.append(x86.Jmp('conclusion'))
        return new_instrs
    
    new_statements = prog.body
    instrs = si_stmts(new_statements)
    return x86.Program({'start': instrs})


##################################################
# assign-homes
##################################################

def assign_homes(program: x86.Program) -> Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocates a stack location for each
    variable in the program.
    :program: An x86 program.
    :return: A Tuple. The first element is an x86 program (with no variable references).
    The second element is the number of bytes needed in stack locations.
    """
    homes = {}
    
    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(i):
                return x86.Immediate(i)
            case x86.Reg(r):
                return x86.Reg(r)
            case x86.Var(x):
                if x in homes:
                    return homes[x]
                else:
                    # create a new stack location for x and add it to homes and then return it
                    offset = - (len(homes) * 8 + 8)
                    homes[x] = x86.Deref('rbp', offset)
                    return homes[x]
            case x86.Deref(offset, val):
                return x86.Deref(offset, val)
            case _:
                return Exception('print_arg', a)
    
    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(name, args):
                new_args = [ah_arg(a) for a in args]
                return x86.NamedInstr(name, new_args)
            case x86.Callq(l):
                return x86.Callq(l)
            case x86.Retq:
                return x86.Retq()
            case x86.Jmp(l):
                return x86.Jmp(l)
            case _:
                return Exception('print_instr', e)
    
    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]
    
    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            # the # of bytes I need to store my variables is already a multiple of 16
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))
    
    blocks = program.blocks
    new_blocks = {}
    for label, block in blocks.items():
        new_blocks[label] = ah_block(block)
    
    stack_locs_used = align(len(homes) * 8)
    return x86.Program(new_blocks), stack_locs_used


##################################################
# patch-instructions
##################################################

def patch_instructions(inputs: Tuple[x86.Program, int]) -> Tuple[x86.Program, int]:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :inputs: A Tuple. The first element is an x86 program. The second element is the stack space in bytes.
    :return: A Tuple. The first element is the patched x86 program. The second element is
    the stack space in bytes.
    """
    homes = {}
    
    def pi_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(i):
                return x86.Immediate(i)
            case x86.Reg(r):
                return x86.Reg(r)
            case x86.Var(x):
                if x in homes:
                    return homes[x]
                else:
                    offset = - (len(homes) * 8 + 8)
                    homes[x] = x86.Deref('rax', offset)
                    return homes[x]
            case x86.Deref(offset, val):
                return x86.Deref(offset, val)
            case _:
                return Exception('print_arg', a)
    
    # return a list of instructions instead of just one instruction
    # for the important case, we can now return two instructions
    # for the other cases, just return a list of length 1
    def pi_instr(e: x86.Instr) -> List[x86.Instr]:
        match e:
            case x86.NamedInstr(name, [x86.Deref(r1, offset1), x86.Deref(r2, offset2)]):
                """
                produce two instructions
                movq Deref(r1, offset1), %rax
                ___q %rax, Deref(r2, offset2)
                """
                return [
                    x86.NamedInstr('movq', [x86.Deref(r1, offset1), x86.Reg('rax')]),
                    x86.NamedInstr(name, [x86.Reg('rax'), x86.Deref(r2, offset2)])
                ]
            case x86.NamedInstr(name, args):
                new_args = [pi_arg(a) for a in args]
                return [x86.NamedInstr(name, new_args)]
            case x86.Callq(l):
                return [x86.Callq(l)]
            case x86.Retq:
                return [x86.Retq()]
            case x86.Jmp(l):
                return [x86.Jmp(l)]
            case _:
                return Exception('print_instr', e)
    
    # change this function to deal with the fact that pi_instr(i) returns a list of instructions
    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_block = []
        for i in instrs:
            [new_block.append(_i) for _i in pi_instr(i)]
        return new_block
    
    _program, stack_bytes_used = inputs
    blocks = _program.blocks
    new_blocks = {}
    for label, block in blocks.items():
        new_blocks[label] = pi_block(block)
    return x86.Program(new_blocks), stack_bytes_used


##################################################
# print-x86
##################################################

def print_x86(inputs: Tuple[x86.Program, int]) -> str:
    """
    Prints an x86 program to a string.
    :inputs: A Tuple. The first element is the x86 program. The second element
    is the stack space in bytes.
    :return: A string, ready for gcc.
    """
    
    def print_arg(arg: x86.Arg) -> str:
        match arg:
            case x86.Immediate(val):
                return f'${val}'
            case x86.Reg(val):
                return f'%{val}'
            case x86.Var(x):
                return f'#{x}'
            case x86.Deref(val, offset):
                return f'{offset}(%{val})'
            case _:
                return Exception('print_arg', arg)
    
    def print_instr(instr: x86.Instr) -> str:
        match instr:
            case x86.NamedInstr(name, args):
                return f'{name} {", ".join([print_arg(a) for a in args])}'
            case x86.Callq(label):
                return f"callq {label}"
            case x86.Jmp(label):
                return f"jmp {label}"
            case _:
                raise Exception('print_instr', instr)
    
    def print_block(label: str, instrs: List[x86.Instr]) -> str:
        return f'{label}:\n' + '\n'.join(['  ' + print_instr(i) for i in instrs])
    
    prog, stack_bytes_used = inputs
    block = prog.blocks
    block_instrs = '\n'.join(print_block(label, block) for label, block in block.items())
    
    out = \
        f"""
  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq ${stack_bytes_used}, %rsp
  jmp start
{block_instrs}
conclusion:
  movq $0, %rax
  addq ${stack_bytes_used}, %rsp
  popq %rbp
  retq
"""
    return out


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
