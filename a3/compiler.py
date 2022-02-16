from ast import *

from collections import defaultdict

from typing import List, Set, Dict, Tuple, DefaultDict
import sys
import itertools
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
    :param prog: An Lvar program
    :return: An Lvar program with atomic operator arguments.
    """
    
    pass


##################################################
# select-instructions
##################################################

def select_instructions(prog: Module) -> x86.Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """
    
    pass


##################################################
# uncover-live
##################################################

def uncover_live(program: x86.Program) -> Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]:
    """
    Performs liveness analysis. Returns the input program, plus live-after sets
    for its blocks.
    :param program: a pseudo-x86 assembly program
    :return: A tuple. The first element is the same as the input program. The
    second element is a dict of live-after sets. This dict maps each label in
    the program to a list of live-after sets for that label. The live-after
    sets are in the same order as the label's instructions.
    """
    '''
    :instr: instruction k+1 in the program
    :live_after: the live-after set of instruction k+1
    '''
    
    # liveness analysis results:
    # for each label in the program:
    #   for each instruction in th block:
    #       what is the live-after set
    
    # returns the set of variables written by instr
    def writes_of(instr: x86.Instr) -> Set[x86.Var]:
        match instr:
            case x86.Callq(_):
                return set()
            case x86.NamedInstr('movq', [_, x86.Var(x)]):
                return set(x86.Var(x))
    
    # return the set of variables read bny instr
    def reads_of(instr: x86.Instr) -> Set[x86.Var]:
        pass
    
    # Inputs:
    # instr: instruction  k + 1 in the program
    # live_after: the live-after set of instruction k + 1 in the program
    # return: the live-after set of instruction k in the program
    def ul_instr(instr: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        pass
    
    # inputs: list of instructions ofr a block
    # output: list of live-after instructions for the block
    def ul_block(label: str, instrs: List[x86.Instr]) -> Tuple[Set[x86.Var]]:
        last_live_after = set()
        live_after_sets = []
        
        for i in reversed(instrs):
            # Start with the empty live-after set for the last instruction
            # Maintain a variable containing the live-after set of the last-processed instruction
            # Build the live-after set for the current instruction, using thg rule above
            #    - You will need to write functions that tell you what variables are written and read by an instruction
            next_live_after = ul_instr(i, last_live_after)
        # Add the new live-after set to the list of live-after sets
        # When finished, reverse the list and return it
        pass
    
    pass


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


def build_interference(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> Tuple[
    x86.Program, InterferenceGraph]:
    """
    Build the interference graph.
    :inputs: A Tuple. The first element is a pseudo-x86 program. The
    second element is the dict of live-after sets produced by the uncover-live
    pass.
    :return: A Tuple. The first element is the same as the input program. The
    second is a completed interference graph.
    """
    prog, live_after_dict = inputs
    
    def bi_instr(instr: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        # pattern match aon the instruction
        # find the var x being written by it
        # for each variable y in live_after
        # call graph.add_edge(x,y)
        pass
    
    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        # pair up each instruction with its live-after set
        for instr, live_after in zip(instrs, live_afters):
            # process instr and its live_after
            pass
    
    # creates an interference graph that we can update during the pass
    interference_graph = InterferenceGraph()
    
    # update the graph
    # use a loop over live_after_dict to call bi_block
    
    # return the graph and original program
    return prog, interference_graph


##################################################
# allocate-registers
##################################################

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]


def allocate_registers(inputs: Tuple[x86.Program, InterferenceGraph]) -> \
    Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param inputs: A Tuple. The first element is the pseudo-x86 program. The
    second element is the completed interference graph.
    :return: A Tuple. The first element is an x86 program (with no variable
    references). The second element is the number of bytes needed in stack
    locations.
    """
    
    pass


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
    
    pass


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
    
    pass


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
