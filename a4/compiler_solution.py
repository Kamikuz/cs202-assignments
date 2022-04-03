from ast import *

from collections import OrderedDict, defaultdict
from typing import List, Set, Dict, Tuple, DefaultDict
import itertools
import sys
import traceback

from cs202_support.base_ast import AST, print_ast

import cs202_support.x86exp as x86
import cif
import constants

gensym_num = 0

# Generates a new unique symbol
def gensym(x):
    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'

# Returns the "simple" name of an object's type
def name_of(op):
    return type(op).__name__

##################################################
# typecheck
##################################################

TEnv = Dict[str, type]

def typecheck(program: Module) -> Module:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param e: The Lif program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        '+':   [int, int],
        'Not': [bool],
        'Or':  [bool, bool],
        'And':  [bool, bool],
        'Gt':   [int, int],
        'Gte':  [int, int],
        'Lt':   [int, int],
        'LtE':  [int, int],
    }

    prim_output_types = {
        '+':   int,
        'Not': bool,
        'Or':  bool,
        'And':  bool,
        'Gt':   bool,
        'Gte':  bool,
        'Lt':   bool,
        'LtE':  bool,
    }


    def tc_exp(e: expr, env: TEnv) -> type:
        match e:
            case Name(x):
                return env[x]
            case Constant(i):
                if isinstance(i, bool):
                    return bool
                elif isinstance(i, int):
                    return int
            case BinOp(e1, Add(), e2):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return int
            case Compare(e1, [Eq()], [e2]):
                t1 = tc_exp(e1, env)
                t2 = tc_exp(e2, env)
                assert t1 == t2
                return bool
            case Compare(e1, [op], [e2]):
                t1 = tc_exp(e1, env)
                t2 = tc_exp(e2, env)
                assert [t1, t2] == prim_arg_types[name_of(op)]
                return prim_output_types[name_of(op)]
            case BoolOp(op, [e1, e2]):
                assert tc_exp(e1, env) == bool
                assert tc_exp(e2, env) == bool
                return prim_output_types[name_of(op)]
            case UnaryOp(Not(), e1):
                assert tc_exp(e1, env) == bool
                return bool
            case _:
                raise Exception('tc_exp', dump(e))

    def tc_stmt(s: stmt, env: TEnv):
        match s:
            case If(condition, then_stmts, else_stmts):
                assert tc_exp(condition, env) == bool

                for s in then_stmts:
                    tc_stmt(s, env)
                for s in else_stmts:
                    tc_stmt(s, env)
            case Expr(Call(Name('print'), [e])):
                tc_exp(e, env)
            case Assign([Name(x)], e):
                t_e = tc_exp(e, env)
                if x in env:
                    assert t_e == env[x]
                else:
                    env[x] = t_e
            case _:
                raise Exception('tc_stmt', dump(s))

    env = {}
    for s in program.body:
        tc_stmt(s, env)

    return program


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
                case If(condition, then_stmts, else_stmts):
                    new_condition = rco_exp(condition, False, bindings)
                    new_then_stmts = rco_stmts(then_stmts)
                    new_else_stmts = rco_stmts(else_stmts)

                    new_stmt = If(new_condition,
                                  new_then_stmts,
                                  new_else_stmts)

                case _:
                    raise Exception('rco_stmt', stmt)

            # (1) add the new bindings created by rco_exp
            new_stmts.extend([Assign([x], e) for x, e in bindings.items()])
            # (2) add the compiled statement itself
            new_stmts.append(new_stmt)

        return new_stmts

    def create_tmp_if_atomic(new_e, atomic, bindings):
        if atomic:
            new_v = Name(gensym('tmp'))
            bindings[new_v] = new_e
            return new_v
        else:
            return new_e
        

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
                return create_tmp_if_atomic(new_e, atomic, bindings)

            case BoolOp(op, args):
                new_args = [rco_exp(e, True, bindings) for e in args]
                new_e = BoolOp(op, new_args)
                return create_tmp_if_atomic(new_e, atomic, bindings)

            case UnaryOp(op, e1):
                new_e1 = rco_exp(e1, True, bindings)
                new_e = UnaryOp(op, new_e1)
                return create_tmp_if_atomic(new_e, atomic, bindings)
                
            case Compare(e1, [op], [e2]):
                new_e1 = rco_exp(e1, True, bindings)
                new_e2 = rco_exp(e2, True, bindings)
                new_e = Compare(new_e1, [op], [new_e2])
                return create_tmp_if_atomic(new_e, atomic, bindings)

            case _:
                raise Exception('rco_exp', e)

    return Module(rco_stmts(prog.body))


##################################################
# explicate-control
##################################################

def explicate_control(prog: Module) -> cif.CProgram:
    """
    Transforms an Lif Expression into a Cif program.
    :param e: An Lif Expression
    :return: A Cif Program
    """

    # the basic blocks of the program
    basic_blocks: Dict[str, List[cif.Stmt]] = {}

    def explicate_exp(e: expr) -> cif.Exp:
        match e:
            case Name(x):
                return cif.Name(x)
            case Constant(c):
                if isinstance(c, bool):
                    return cif.ConstantBool(c)
                elif isinstance(c, int):
                    return cif.ConstantInt(c)
            case BinOp(e1, op, e2):
                return cif.BinOp(explicate_exp(e1),
                                 op,
                                 explicate_exp(e2))
            case Compare(e1, [op], [e2]):
                return cif.Compare(explicate_exp(e1),
                                   op,
                                   explicate_exp(e2))
            case BoolOp(op, [e1, e2]):
                return cif.BinOp(explicate_exp(e1),
                                 op,
                                 explicate_exp(e2))
            case UnaryOp(Not(), e1):
                return cif.UnaryOp(Not(), explicate_exp(e1))
            case _:
                raise RuntimeError(dump(e))

    def add_stmt(label: str, s: stmt):
        if label not in basic_blocks:
            basic_blocks[label] = []

        basic_blocks[label].append(s)

    def explicate_stmts(stmts: List[stmt],
                        current_label: str, cont_label: str):
        for s in stmts:
            match s:
                case Assign([Name(x)], exp):
                    new_exp = explicate_exp(exp)
                    add_stmt(current_label, cif.Assign(x, new_exp))
                case Expr(Call(Name('print'), [exp])):
                    new_exp = explicate_exp(exp)
                    add_stmt(current_label, cif.Print(new_exp))

                case If(cond, then_stmts, else_stmts):
                    # compile the condition (as an expression)
                    new_cond = explicate_exp(cond)

                    # create labels for the then and else branches
                    then_label = gensym('label')
                    else_label = gensym('label')
                    # create a label for the "rest of the stuff"
                    new_cont_label = gensym('label')

                    # create an if statement that:
                    # 1. evaluates the condition
                    # 2. compares the condition to "True"
                    # 3. jumps to the then and else branches based on the result
                    match new_cond:
                        # comparison (common case)
                        case cif.Compare(_, _, _):
                            add_stmt(current_label, cif.If(new_cond,
                                                        cif.Goto(then_label),
                                                        cif.Goto(else_label)))
                        case e:
                            tmp = gensym('tmp')
                            add_stmt(current_label, cif.Assign(tmp, e))
                            add_stmt(current_label, cif.If(cif.Compare(cif.Name(tmp), Eq(),
                                                                       cif.ConstantBool(True)),
                                                        cif.Goto(then_label),
                                                        cif.Goto(else_label)))

                    # compile the then and else branch, adding a basic block for each one
                    explicate_stmts(then_stmts, then_label, new_cont_label)
                    explicate_stmts(else_stmts, else_label, new_cont_label)

                    # when we compile future statements, they should go in the basic
                    # block corresponding to the "rest of the stuff"
                    current_label = new_cont_label
                    
                case _:
                    raise RuntimeError(dump(s))

        # if there is nothing left to do, jump to the "rest of the stuff to do" label
        add_stmt(current_label, cif.Goto(cont_label))

    new_stmts = explicate_stmts(prog.body, 'start', 'conclusion')
    return cif.CProgram(basic_blocks)


##################################################
# select-instructions
##################################################

def select_instructions(p: cif.CProgram) -> x86.Program:
    """
    Transforms a Cif program into a pseudo-x86 assembly program.
    :param p: a Cif program
    :return: a pseudo-x86 program
    """

    def si_atm(a: cif.Atm) -> x86.Arg:
        match a:
            case cif.ConstantInt(i):
                return x86.Immediate(i)
            case cif.ConstantBool(i):
                if i == True:
                    return x86.Immediate(1)
                else:
                    return x86.Immediate(0)
            case cif.Name(x):
                return x86.Var(x)
            case _:
                raise Exception('si_atm', a)

    op_cc = {
        'Eq': 'e',
        'Gt': 'g',
        'Lt': 'l',
        'LtE': 'le',
    }

    boolop_instrs = {
        'And': 'andq',
        'Or': 'orq',
    }

    def si_stmts(stmts: List[cif.Stmt]) -> List[x86.Instr]:
        instrs = []

        for s in stmts:
            match s:
                case cif.If(cif.Compare(e1, op, e2),
                            cif.Goto(then_label),
                            cif.Goto(else_label)):
                    
                    instrs += [x86.NamedInstr('cmpq', [si_atm(e2), si_atm(e1)]),
                               x86.JmpIf(op_cc[name_of(op)], then_label),
                               x86.Jmp(else_label)]
                case cif.Print(e):
                    instrs += [x86.NamedInstr('movq', [si_atm(e), x86.Reg('rdi')]),
                               x86.Callq('print_int')]
                case cif.Goto(label):
                    instrs += [x86.Jmp(label)]
                case cif.Assign(x, cif.BinOp(e1, Add(), e2)):
                    instrs += [x86.NamedInstr('movq', [si_atm(e1), x86.Var(x)]),
                               x86.NamedInstr('addq', [si_atm(e2), x86.Var(x)])]
                case cif.Assign(x, cif.BinOp(e1, op, e2)):
                    instr_name = boolop_instrs[name_of(op)]
                    instrs += [x86.NamedInstr('movq', [si_atm(e1), x86.Var(x)]),
                               x86.NamedInstr(instr_name, [si_atm(e2), x86.Var(x)])]
                case cif.Assign(x, cif.Compare(e1, op, e2)):
                    instrs += [x86.NamedInstr('cmpq', [si_atm(e2), si_atm(e1)]),
                               x86.Set(op_cc[name_of(op)], x86.ByteReg('al')),
                               x86.NamedInstr('movzbq', [x86.ByteReg('al'), x86.Var(x)])]
                case cif.Assign(x, cif.UnaryOp(Not(), e1)):
                    instrs += [x86.NamedInstr('movq', [si_atm(e1), x86.Var(x)]),
                               x86.NamedInstr('xorq', [x86.Immediate(1), x86.Var(x)])]
                case cif.Assign(x, cif.ConstantInt(i)):
                    instrs.append(x86.NamedInstr('movq', [x86.Immediate(i), x86.Var(x)]))
                case cif.Assign(x, cif.ConstantBool(b)):
                    instrs.append(x86.NamedInstr('movq', [x86.Immediate(int(b)), x86.Var(x)]))
                case cif.Assign(x, cif.Name(y)):
                    instrs.append(x86.NamedInstr('movq', [x86.Var(y), x86.Var(x)]))
                case _:
                    raise RuntimeError(s)

        return instrs

    return x86.Program({label: si_stmts(block) for (label, block) in p.blocks.items()})


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

    live_before_sets = {'conclusion': set()}
    live_after_sets = {}
    blocks = program.blocks

    def vars_arg(a: x86.Arg) -> Set[x86.Var]:
        match a:
            case x86.Immediate(i):
                return set()
            case x86.Reg(r):
                return set()
            case x86.ByteReg(r):
                return set()
            case x86.Var(x):
                return {x86.Var(x)}
            case _:
                raise Exception('ul_arg', a)

    def reads_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('movq', [e1, e2]):
                return vars_arg(e1)
            case x86.NamedInstr('addq', [e1, e2]):
                return vars_arg(e1).union(vars_arg(e2))
            case x86.NamedInstr('cmpq', [e1, e2]):
                return vars_arg(e1).union(vars_arg(e2))
            case x86.NamedInstr('movzbq', [e1, e2]):
                return vars_arg(e1)
            case x86.Jmp(label) | x86.JmpIf(_, label):
                # if we don't know the live-before set for the destination,
                # calculate it first
                if label not in live_before_sets:
                    ul_block(label)

                # the variables that might be read after this instruction
                # are the live-before variables of the destination block
                return live_before_sets[label]
            case _:
                return set()

    def writes_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('movq', [e1, e2]):
                return vars_arg(e2)
            case x86.NamedInstr('addq', [e1, e2]):
                return vars_arg(e2)
            case x86.NamedInstr('movzbq', [e1, e2]):
                return vars_arg(e2)
            case _:
                return set()

    def ul_instr(i: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        return live_after.difference(writes_of(i)).union(reads_of(i))

    def ul_block(label: str):
        instrs = blocks[label]
        current_live_after: Set[x86.Var] = set()

        block_live_after_sets = []
        for i in reversed(instrs):
            block_live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after)

        live_before_sets[label] = current_live_after
        live_after_sets[label] = list(reversed(block_live_after_sets))


    ul_block('start')
    return program, live_after_sets


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


def build_interference(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> \
        Tuple[x86.Program, InterferenceGraph]:
    """
    Build the interference graph.
    :param inputs: A Tuple. The first element is a pseudo-x86 program. The
    second element is the dict of live-after sets produced by the uncover-live
    pass.
    :return: A Tuple. The first element is the same as the input program. The
    second is a completed interference graph.
    """

    def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        match e:
            case x86.NamedInstr(_, [e1, x86.Var(x)]):
                for var in live_after:
                    graph.add_edge(x86.Var(x), var)
            case x86.Set(cc, x86.Var(x)):
                for var in live_after:
                    graph.add_edge(x86.Var(x), var)
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf, x86.NamedInstr, x86.Set)):
                    pass
                else:
                    raise Exception('bi_instr', e)

    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        for instr, live_after in zip(instrs, live_afters):
            bi_instr(instr, live_after, graph)

    program, live_after_sets = inputs
    blocks = program.blocks

    interference_graph = InterferenceGraph()

    for label in blocks.keys():
        bi_block(blocks[label], live_after_sets[label], interference_graph)

    return program, interference_graph


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

    ## Functions for graph coloring
    def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:
        coloring: Coloring = {}

        to_color = local_vars.copy()

        # Saturation sets start out empty
        saturation_sets = {x: set() for x in local_vars}

        # Loop until we are finished coloring
        while to_color:
            # Find the variable x with the largest saturation set
            x = max(to_color, key=lambda x: len(saturation_sets[x]))

            # Remove x from the variables to color
            to_color.remove(x)

            # Find the smallest color not in x's saturation set
            x_color = next(i for i in itertools.count() if i not in saturation_sets[x])

            # Assign x's color
            coloring[x] = x_color

            # Add x's color to the saturation sets of its neighbors
            for y in interference_graph.neighbors(x):
                saturation_sets[y].add(x_color)

        return coloring

    # Functions for allocating registers
    def make_stack_loc(offset):
        return x86.Deref('rbp', -(offset * 8))

    # Functions for replacing variables with their homes
    homes: Dict[str, x86.Arg] = {}

    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(i):
                return a
            case x86.Reg(r):
                return a
            case x86.ByteReg(r):
                return a
            case x86.Var(x):
                if a in homes:
                    # If we have assigned x a home, return it
                    return homes[a]
                else:
                    # Otherwise we can use any register; use r12
                    return x86.Reg('r12')
            case _:
                raise Exception('ah_arg', a)

    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(i, args):
                new_args = [ah_arg(a) for a in args]
                return x86.NamedInstr(i, new_args)
            case x86.Set(cc, a1):
                return x86.Set(cc, ah_arg(a1))
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf)):
                    return e
                else:
                    raise Exception('ah_instr', e)

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]

    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))

    # Main body of the pass
    program, interference_graph = inputs
    blocks = program.blocks

    # Variables in the interference graph
    local_vars = set(interference_graph.graph.keys())

    # Color the graph
    coloring = color_graph(local_vars, interference_graph)
    colors_used = set(coloring.values())

    # Defines the set of registers to use
    available_registers = constants.caller_saved_registers + constants.callee_saved_registers

    # Create the color map
    color_map = {}
    stack_locations_used = 0

    for color in colors_used:
        if available_registers != []:
            r = available_registers.pop()
            color_map[color] = x86.Reg(r)
        else:
            color_map[color] = make_stack_loc(stack_locations_used)
            stack_locations_used += 1

    # Compose the two mappings to get "homes"
    for v in local_vars:
        color = coloring[v]
        homes[v] = color_map[color]

    blocks = program.blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}
    return x86.Program(new_blocks), align(8 * stack_locations_used)


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
            case x86.NamedInstr(i, [x86.Deref(_, _), x86.Deref(_, _)]):
                return [x86.NamedInstr('movq', [e.args[0], x86.Reg('rax')]),
                        x86.NamedInstr(i, [x86.Reg('rax'), e.args[1]])]
            case x86.NamedInstr('movzbq', [_, x86.Deref(_, _)]):
                    return [x86.NamedInstr('movzbq', [e.args[0], x86.Reg('rax')]),
                            x86.NamedInstr('movq', [x86.Reg('rax'), e.args[1]])]
            case x86.NamedInstr('cmpq', [a1, x86.Immediate(i)]):
                return [x86.NamedInstr('movq', [x86.Immediate(i), x86.Reg('rax')]),
                        x86.NamedInstr('cmpq', [a1, x86.Reg('rax')])]
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf, x86.NamedInstr, x86.Set)):
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
            case x86.ByteReg(r):
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
            case x86.JmpIf(cc, label):
                return f'j{cc} {label}'
            case x86.Set(cc, a1):
                return f'set{cc} {print_arg(a1)}'
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
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'explicate control': explicate_control,
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

