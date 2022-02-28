import itertools
from ast import *

from collections import defaultdict

from typing import List, Set, Dict, Tuple, DefaultDict
import sys
import traceback

from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86
import constants

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
    :prog: An Lvar program
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
# uncover-live
##################################################


def uncover_live(program: x86.Program) -> Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]:
    """
    Performs liveness analysis. Returns the input program, plus live-after sets
    for its blocks.
    :program: a pseudo-x86 assembly program
    :return: A tuple. The first element is the same as the input program. The
    second element is a dict of live-after sets. This dict maps each label in
    the program to a list of live-after sets for that label. The live-after
    sets are in the same order as the label's instructions.
    """
    '''
    :instr: instruction k+1 in the program
    :live_after: the live-after set of instruction k+1
    '''
    """
    Inputs
    instr: instruction k + 1 in the program
    live_after: the live-after set of instruction k + 1 in the program
    return: the live-after set of instruction k in the program
    to implement: use the equation
    """
    
    # returns the set of variables written by instr
    def writes_of(instr: x86.Instr) -> Set[x86.Var]:
        match instr:
            case x86.NamedInstr('movq', [_, x86.Var(x)]):
                return {x86.Var(x)}
            case x86.NamedInstr('addq', [x86.Var(x), x86.Var(y)]):
                return {x86.Var(x), x86.Var(y)}
            case _:
                return set()
    
    # return the set of variables read by instr
    def reads_of(instr: x86.Instr) -> Set[x86.Var]:
        match instr:
            case x86.NamedInstr('movq', [x86.Var(x), _]):
                return {x86.Var(x)}
            case x86.NamedInstr('addq', [x86.Var(x), x86.Var(y)]):
                return {x86.Var(y), x86.Var(x)}
            case _:
                return set()
    
    # Inputs:
    # instr: instruction  k + 1 in the program
    # live_after: the live-after set of instruction k + 1 in the program
    # return: the live-after set of instruction k in the program
    def ul_instr(instr: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        w = writes_of(instr)
        r = reads_of(instr)
        return live_after.difference(w).union(r)
    
    # inputs: list of instructions of a block
    # output: list of live-after instructions for the block
    def ul_block(instrs: List[x86.Instr]) -> Tuple[Set[x86.Var]]:
        last_live_after = set()
        live_after_sets = []
        for i in reversed(instrs):
            live_after_sets.append(last_live_after)
            last_live_after = ul_instr(i, last_live_after)
        return list(reversed(live_after_sets))
    
    # for each block in the program:
    #   call ul_block on the block to ger the live-after sets for that block
    
    blocks = program.blocks
    all_live_after_sets: Dict[str, List[Set[x86.Var]]] = {label: ul_block(block) for label, block in blocks.items()}
    return program, all_live_after_sets


##################################################
# build-interference
##################################################
class InterferenceGraph:
    """
    A class to represent an interference graph: an undirected graph where nodes
    are x86.Arg objects and an edge between two nodes indicates that the two
    nodes cannot share the same locations.
    """
    graph: DefaultDict[x86.Arg, Set[x86.Arg]]
    
    def __init__(self):
        self.graph = defaultdict(lambda: set())
    
    def add_edge(self, a: x86.Arg, b: x86.Arg):
        if a != b:
            self.graph[a].add(b)
            self.graph[b].add(a)
    
    def neighbors(self, a: x86.Arg) -> Set[x86.Arg]:
        if a in self.graph:
            return self.graph[a]
        else:
            return set()
    
    def __str__(self):
        pairs = set()
        for k in self.graph.keys():
            new_pairs = set((k, v) for v in self.graph[k])
            pairs = pairs.union(new_pairs)
        
        for a, b in list(pairs):
            if (b, a) in pairs:
                pairs.remove((a, b))
        
        strings = [print_ast(a) + ' -- ' + print_ast(b) for a, b in pairs]
        return 'InterferenceGraph{\n ' + ',\n '.join(strings) + '\n}'


def build_interference(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> Tuple[x86.Program,
                                                                                           InterferenceGraph]:
    """
    Build the interference graph.
    :inputs: A Tuple. The first element is a pseudo-x86 program. The
    second element is the dict of live-after sets produced by the uncover-live
    pass.
    :return: A Tuple. The first element is the same as the input program. The
    second is a completed interference graph.
    """
    
    # update the interference graph based on a single instruction
    def bi_instr(instr: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        # pattern match aon the instruction
        # find the var x being written by it
        # for each variable y in live_after
        # call graph.add_edge(x,y)
        match instr:
            case x86.NamedInstr('movq', [_, x86.Var(x)]):
                for y in live_after:
                    graph.add_edge(x86.Var(x), y)
            case x86.NamedInstr('addq', [_, x86.Var(x)]):
                for y in live_after:
                    graph.add_edge(x86.Var(x), y)
    
    # update the interference graph based on a program block with a list of instructions
    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        # pair up each instruction with its live-after set
        for instr, live_after in zip(instrs, live_afters):
            # process instr and its live_after
            bi_instr(instr, live_after, graph)
    
    prog, live_after_dict = inputs
    # update the graph
    # creates an interference graph that we can update during the pass
    interference_graph = InterferenceGraph()
    
    # use a loop over live_after_dict to call bi_block
    for label, live_afters in live_after_dict.items():
        bi_block(prog.blocks[label], live_after_dict[label], interference_graph)
    # return the graph and original program
    return prog, interference_graph


##################################################
# allocate-registers
##################################################

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]


def allocate_registers(inputs: Tuple[x86.Program, InterferenceGraph]) -> Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocate registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :inputs: A Tuple. The first element is the pseudo-x86 program. The second element is the completed interference
    graph.
    :return: A Tuple. The first element is an x86 program (with no variable
    references). The second element is the number of bytes needed in stack
    locations.
    """
    prog, interference_graph = inputs
    
    # 1. Color the interference graph, to obtain mapping from vars -> colors
    def color_graph(vars: List[x86.Var], graph: InterferenceGraph) -> Coloring:
        # maps each variable to its saturation set
        saturation_sets: Dict[x86.Var, Set[Color]] = {x: set() for x in vars}
        
        coloring: Coloring = {}
        # Do until all vars have a color:
        while vars:
            #   1. Pick var x with the largest saturation set (breaking ties randomly / in any order)
            x = max(vars, key=lambda v: (len(saturation_sets[v])))
            vars.remove(x)
            #   2. Assign x the lowest color c not in x's saturation set
            color_chosen = next(i for i in itertools.count() if i not in saturation_sets[x])
            coloring[x] = color_chosen
            #   3. Add c to the saturation sets of x's neighbors
            for y in graph.neighbors(x):
                saturation_sets[y].add(color_chosen)
        
        # create a coloring
        return coloring
    
    # 2. Build mapping from colors -> locs, using registers when possible and stack locations when you run out
    graph_vars = list(interference_graph.graph.keys())
    coloring: Coloring = color_graph(graph_vars, interference_graph)
    available_registers = constants.callee_saved_registers + constants.caller_saved_registers
    color_map: Dict[Color, x86.Arg] = {}
    stack_locations_used = 0
    
    for color in coloring.values():
        # use a register if one is available
        # otherwise generate a new stack location and use that
        if color in available_registers:
            color_map[color] = color
        else:
            color_map[color] = x86.Deref('rbp', -(stack_locations_used * 8))
            stack_locations_used += 1
    
    # 3. Compose the mapping from (1) and (2) to obtain homes: a mapping form vars -> locs
    homes = {}
    for var in coloring:
        color_for_this_var = coloring[var]
        homes[var] = color_map[color_for_this_var]
    
    # 4. Use the logic form assign-homes in A2 to replace variables with their locations using the homes created in (3)
    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))
    
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
                    return x86.Reg('rdx')
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
    
    blocks = prog.blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}
    return x86.Program(new_blocks), align(8 * max(0, stack_locations_used - len(available_registers)))


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
    'uncover live': uncover_live,
    'build interference': build_interference,
    'allocate registers': allocate_registers,
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
