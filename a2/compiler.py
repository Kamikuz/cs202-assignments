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
    
    def rco_statms(statms: List[stmt]) -> List[stmt]:
        new_statements = []
        for s in statms:
            bindings = {}
            # call rco_exp based on the type of s
            # e.g. rco_exp(e, bindings, False)
            # add assignment atatsmnets to new_statements base on the bindings
            # add a new version of the original statment s to new_statments
            pass
    
    def rco_exp(e: expr, bindings: Dict[str, expr], atomic: bool) -> expr:
        match e:
            case Constant(i):
                return Constant(i)
            case BinOp(e1, Add(), e2):
                new_e1 = rco_exp(e1, bindings, True)
                new_e2 = rco_exp(e2, bindings, True)
                
                if atomic:
                    # create new tmp varibale
                    pass
                else:
                    # return the new binop expression
                    return BinOp(new_e1, Add(), new_e2)
    
    new_statements = rco_statms(prog.body)
    return Module(new_statements)


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
        instrs = []
        for s in statements:
            match s:
                case Assign([Name(var)], BinOp(a1, Add(), a2)):
                    pass
                case Assign([Name(var)], exp):
                    pass
                case Expr(Call(Name('print'), [a1])):
                    new_instrs = [
                        x86.NamedInstr('movq', [si_arg(a1), x86.Reg('rdi')]),
                        x86.Callq('print_int'),
                    ]
                    instrs.append(new_instrs)
        return instrs
    
    statemnets = prog.body
    instrs = si_stmts(statemnets)
    # return x86 porgram with these instructions


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
    homes = Dict[str, x86.Arg] = {}
    
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
                    pass
    
    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(name, args):
                new_args = [ah_arg(a) for a in args]
                return x86.NamedInstr(name, new_args)
            case x86.Callq(label):
                return f'callq {label}'
            case x86.Retq:
                return f'retq'
            case x86.Jmp(label):
                return f'jmp{label}'
            case _:
                return Exception('print_instr', e)
    
    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]
    
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
    :param inputs: A Tuple. The first element is an x86 program. The second element is the
    stack space in bytes.
    :return: A Tuple. The first element is the patched x86 program. The second element is
    the stack space in bytes.
    """
    
    # return a list of instuctions instead of just one instuction
    # for the important case, we can now return tow instauctions
    # for the other cases, just return a list of length 1
    def pi_instr(e: x86.Instr) -> List[x86.Instr]:
        match e:
            case x86.NamedInstr(name, [Deref(r1, offset1), Deref(r2, offset2)]):
                # produce two instructions
                # movq Deref(r1, offset1), %rax
                # ___q %ras, Deref(r2, offset2)
                pass
            case x86.NamedInstr(name, args):
                new_args = [ah_arg(a) for a in args]
                return [x86.NamedInstr(name, new_args)]
            case x86.Callq(label):
                return f'callq {label}'
            case x86.Retq:
                return f'retq'
            case x86.Jmp(label):
                return f'jmp{label}'
            case _:
                return Exception('print_instr', e)
    
    # change this function to deal with the fact that pi_instr(i) rteurns a list of insturctions
    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [pi_instr(i) for i in instrs]
    
    program, stack_bytes_used = inputs
    blocks = program.blocks
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
    :param inputs: A Tuple. The first element is the x86 program. The second element
    is the stack space in bytes.
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
    
    def print_block(label: str, instrs: List[x86.Instr]) -> str:
        name = f'{label}:\n'
        instr_strs = '\n'.join(['  ' + print_instr(i) for i in instrs])
        return name + instr_strs
    
    program, stack_bytes_used = inputs
    block = program.blocks
    block_instrs = '\n'.join(print_block(label, block) for label, block in block.items())
    
    out = f"""
    .globl main
  main:
    pushq %rbp
    movq %rsp, %rbp
    subq ${stack_bytes_used}
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
