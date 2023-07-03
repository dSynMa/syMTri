#!/usr/bin/env python3

from collections import Counter, deque
from copy import deepcopy
from dataclasses import dataclass
from enum import Enum
from itertools import chain, combinations
from operator import add, mul, sub

from pysmt.shortcuts import (FALSE, GE, GT, LE, LT, And, Bool, Implies, Int,
                             Not, Or, Symbol, get_free_variables, get_type,
                             simplify, substitute)
from pysmt.typing import BOOL, INT
from tatsu.grammars import Grammar
from tatsu.objectmodel import Node
from tatsu.semantics import ModelBuilderSemantics
from tatsu.tool import compile
from tatsu.walkers import NodeWalker



def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))  # noqa: E501


class Token(Enum):
    ADD     = "+"
    SUB     = "-"
    MUL     = "*"
    DIV     = "/"
    GT      = ">"
    LT      = "<"
    GE      = ">="
    LE      = "<="
    EQ      = "=="
    AND     = "&&"
    OR      = "||"
    IMPL    = "=>"
    NOT     = "!"


class BaseNode(Node):
    def unparse(self) -> str:
        return NotImplementedError()


class Store(BaseNode):
    name = None


class Expr(BaseNode):
    pass


class Literal(Expr):
    value = None

    def get_type(self):
        return "bool" if isinstance(self.value, bool) else "int"


class Load(Expr):
    name = None


class Operation(Expr):
    def __init__(self, ast=None, **attributes):
        super().__init__(ast, **attributes)
        self.op = Token(self.op)


class BinOp(Operation):
    left = None
    op = None
    right = None


class Increment(BaseNode):
    var_name = None


class Decrement(BaseNode):
    var_name = None


class UnaryOp(Operation):
    op = None
    expr = None


class Comparison(BinOp):
    pass


class BinLogic(BinOp):
    pass


class If(BaseNode):
    cond = None
    body = None
    or_else = None


class Assign(BaseNode):
    lhs = None
    rhs = None

    def __repr__(self) -> str:
        return self.unparse()

    def __str__(self):
        return self.unparse()

    def unparse(self) -> str:
        return f"{self.lhs} := {self.rhs};"


class Decl(BaseNode):
    var_type = None
    var_name = None
    init = None
    io = None


class EnumDef(BaseNode):
    name = None
    values = None


class MethodDef(BaseNode):
    name = None
    kind = None
    params = None
    precond = None
    decls = None
    body = None


class Program(BaseNode):
    decls = None
    enums = None
    methods = None


GRAMMAR = '''
@@grammar::POPL
@@keyword :: assert assume else enum extern false if intern method true
@@eol_comments :: /\/\/.*?$/


start::Program =
    { decls+:global_decl | enums+:enum_def }*
    methods:{ method_extern | method_intern }+
    $
    ;

enum_def::EnumDef =
    'enum' ~ name:identifier '{'  values:','.{identifier}+ '}' ';'
    ;

decl::Decl =
    var_type:identifier var_name:identifier ':=' init:expression ';'
    ;

global_decl::Decl
    =
    [io:'output'] >decl
    ;

signature =
    name:identifier '(' params:','.{ parameter }* ')'
    ;

parameter::Decl = var_type:identifier var_name:identifier init:()
    ;

method_body
    =
    decls: { decl }*
    body:{ statement }*
;

method_extern::MethodDef =
    'method' kind:'extern' ~ >signature '{'
    precond:{ assumption }*
    >method_body
    '}'
    node_type:`method_extern`
    ;

method_intern::MethodDef =
    'method' kind:'intern' ~ >signature '{'
    precond:{ assertion }*
    >method_body
    '}'
    node_type:`method_intern`
    ;



assumption = 'assume' '(' @:expression ')' ';' ;
assertion = 'assert' '(' @:expression ')' ';' ;

statement =
    | if
    | '{' @:{ statement }* '}'
    | assignment
    | incr
    | decr
    ;

incr::Increment = var_name:lhs '++' ';' ;
decr::Decrement = var_name:lhs '--' ';' ;

assignment::Assign = lhs:lhs ':=' rhs:expression ';' ;

if::If = 'if' ~ '(' cond:expression ')' body:statement ['else' or_else:statement] ;

lhs::Store = name:identifier ;

expression
    =
    | binary_logic_op
    | comparison
    ;

binary_logic_op::BinLogic
    =
    left:expression op:('&&'|'||'|'=>') ~ right:comparison
    ;

# equality = eq_or_neq | comparison ;
# eq_or_neq::Comparison
#     =
#     left:equality op:('=='|'!=') ~ right:comparison
#     ;

comparison
    =
    | compare_op
    | arithmetic
    ;

compare_op::Comparison
    =
    left:arithmetic op:('>'|'<'|'=='|'!=') ~ right:arithmetic
    ;

arithmetic
    =
    | add_or_sub
    | term
    ;

add_or_sub::BinOp
    =
    | left:arithmetic op:'+' ~ right:term
    | left:arithmetic op:'-' ~ right:term
    ;

term
    =
    | mul_or_div
    | factor
    ;

mul_or_div::BinOp
    =
    | left:term op:'*' right:factor
    | left:term op:'/' right:factor
    ;

factor
    =
    | '(' ~ @:expression ')'
    | unary
    | bool_lit
    | number_lit
    | var_reference
    ;

unary::UnaryOp
    =
    | op:'!' expr:expression
    | op:'-' expr:expression
    ;

var_reference::Load = name:identifier ;

@name
identifier = /\_?[a-zA-Z][a-zA-Z0-9\_]*/;

bool_lit::Literal = value:(true|false) ;
true::bool = 'true' ;
# For false, we use @:() to return None
# so that bool(None) gives us False
false::bool = 'false' ~ @:() ;

number_lit::Literal = value:number ;
number::int = /[0-9]+/ ;
'''

# test = """
#     bool x := false;
#     bool y := true;
#     int z := 0;
#     //enum foo { bar, baz };
#     //foo myFoo := baz;

#     method extern foo (bool param) {
#         // This is a comment
#         assume(z > 1 && z < 4);
#         int localInteger := 0 ;
#         z := 2*z;

#         if (z > 10) {
#             z := 5*z; y := z > 4;
#         } else {

#         }

#         z := z+1;
#     }
#     method intern bar () {
#         x := true;
#         if (x) {
#             if (z>10) z := z + 1;
#         } else {
#             x := x; y := x;
#         }
#     }
# """


test = """
int cars_from_left := 0;
int cars_from_right := 0;
output bool danger := false;
output bool closed_from_left := true;
output bool closed_from_right := true;
output bool change_direction := false;

method extern sensor_update(bool car_from_left_entry, bool car_from_right_entry,
                                bool car_from_left_exit, bool car_from_right_exit,
                                bool _change_direction){
    assume(closed_from_left => !car_from_left_entry);
    assume(closed_from_right => !car_from_right_entry);

    if (car_from_left_entry) cars_from_left++;

    if (car_from_right_entry) cars_from_right++;

    if (car_from_left_exit) cars_from_left--;

    if (car_from_right_exit) cars_from_right--;

    change_direction := _change_direction;

    danger := cars_from_left > 0 && cars_from_right > 0;
}

method intern control(bool close_from_left, bool close_from_right){
    closed_from_left := close_from_left;
    closed_from_right := close_from_right;
}
"""


@dataclass
class SymbolTableEntry:
    name: str
    context: 'SymbolTable'
    init: any
    type_: any
    ast: Decl


class SymbolTable:
    GLOBAL_CTX = "<global>"
    def __init__(self, name=GLOBAL_CTX, parent=None, is_params=False):
        self.name = name
        self.parent = parent
        self.children = []
        self.symbols = {}
        self.is_params = is_params

    def __getitem__(self, key):
        return self.symbols[key]

    def __contains__(self, key):
        return key in self.symbols

    def __str__(self) -> str:
        return f"{self.name}:{self.symbols}"

    def add_child(self, name, is_params=False):
        name = name + "##params" if is_params else name
        table = SymbolTable(name, parent=self, is_params=is_params)
        self.children.append(table)
        return table

    def is_local(self):
        return self.parent is not None and not self.is_params

    def lookup(self, name) -> SymbolTableEntry:
        if name in self.symbols:
            return self.symbols[name]
        elif self.parent is None:
            print(self)
            raise KeyError(f"Symbol {name} not found")
        else:
            return self.parent.lookup(name)

    def add(self, node: Decl, init) -> SymbolTableEntry:
        builtin_types = {'int': INT, 'bool': BOOL}
        symbol = SymbolTableEntry(
            node.var_name, self, init, builtin_types[node.var_type], node)
        self.symbols[node.var_name] = symbol
        return symbol


class ForkingPath:
    def __init__(self, parent=None) -> None:
        self.variables = {}
        self.counters = Counter() if parent is None else deepcopy(parent.counters)  # noqa: E501
        self.assignments = {}
        # self.assignments = []
        self.conditions = []
        self.children = []
        self.parent = parent

    def _lookup(self, name):
        if name in self.variables:
            return self.variables[name]
        return None if self.parent is None else self.parent._lookup(name)

    def fresh(self, name, table):
        symbol = table.lookup(name)
        self.variables[name] = Symbol(f"{name}#{self.counters[name]}", symbol.type_)  # noqa: E501
        self.counters[name] += 1
        return self.variables[name]

    def lookup_or_fresh(self, name, table):
        return self._lookup(name) or self.fresh(name, table)

    def add_child(self):
        child = ForkingPath(self)
        self.children.append(child)
        return child

    def get_root(self):
        return self if self.parent is None else self.parent.get_root()

    def leaves(self, start_from=None):
        def descend(n):
            if not n.children:
                yield n
            else:
                for child in n.children:
                    yield from descend(child)
        yield from descend(start_from or self)

    def get_path(self):
        n = self
        conds, asgns = [], {}
        while n is not None:
            conds.extend(n.conditions)
            asgns.update(n.assignments)
            n = n.parent
        return conds, asgns

    def to_transition(self, table: SymbolTable):
        conds, asgns = self.get_path()
        subs = []
        local_inits = {}
        for x in asgns:
            name, version = str(x)[1:-1].split("#")
            version = int(version)
            if 0 < version < self.counters[name] - 1:
                # This is neither the 1st or last version of x
                subs.append(x)
            else:
                # Always add x if it is local (= not global nor parameter)
                symb: SymbolTableEntry = table.lookup(name)
                if symb.context.is_local():
                    subs.append(x)
                    # Add information about initial value of x
                    if version == 0:
                        local_inits[x] = symb.init
        asgns.update(local_inits)

        # We topologically sort variables so that we
        # can do the substitution in a single pass
        topo_sort = []
        unsorted = deque(subs)
        while unsorted:
            var = unsorted.popleft()
            if any(var in get_free_variables(asgns[x]) for x in unsorted):
                unsorted.append(var)
            else:
                topo_sort.append(var)

        # Substitute and remove intermediate variables
        for x in topo_sort:
            sub = {x: asgns[x]}
            for y in asgns:
                asgns[y] = substitute(asgns[y], sub)
            conds = [
                substitute(f, {x: asgns[x]})
                for f in conds]
        for x in subs:
            del asgns[x]

        def remove_version(var):
            return Symbol(var.symbol_name().split("#")[0], get_type(var))

        def remove_all_versions(formula):
            fvs = get_free_variables(formula)
            return substitute(formula, {fv: remove_version(fv) for fv in fvs})

        conds = [remove_all_versions(f) for f in conds]
        action = {
            remove_version(x): remove_all_versions(asgns[x])
            for x in asgns}

        # Branch on output variables and yield
        output_vars = {
            x: action[x] for x in action
            if table.lookup(x.symbol_name()).ast.io == "output"}

        actions_wo_out = {x: action[x] for x in action if x not in output_vars}
        for positive_out in powerset(output_vars):
            negated_out = {x for x in output_vars if x not in positive_out}
            new_conds = [c for c in conds]
            new_conds.extend(action[o] for o in positive_out)
            new_conds.extend(Not(action[o]) for o in negated_out)
            yield new_conds, actions_wo_out, positive_out


    def prune(self):
        for x in self.leaves(self.get_root()):
            conds, _ = x.get_path()
            if simplify(And(conds)) == FALSE():
                # print(f"{conds} is unsat, pruning {x} away")
                x.parent.children.remove(x)

    def pprint(self) -> str:
        conds, asgns = self.get_path()
        return f"{conds}-->{asgns}"


class Walker(NodeWalker):

    def __init__(self):
        super().__init__()
        self._reset_paths()
        self.table = SymbolTable()
        self.symbols = {}

    def _reset_paths(self):
        self.fp = ForkingPath()

    def push(self, frame):
        self.ctx.append(frame)

    def pop(self):
        return self.ctx.pop()

    def context(self):
        return self.ctx[-1]

    def walk_Decl(self, node: Decl):
        init = self.walk(node.init)
        self.table.add(node, init)
        if self.table.parent is not None and node.init is not None:
            var = self.fp.fresh(node.var_name, self.table)
            self.fp.assignments[var] = init
        # elif "##params" in self.table.name:
        #     # This is a parameter
        #     for x in self.fp.leaves(self.fp.get_root()):
        #         var = x.fresh(node.var_name, self.table)
        #         child1 = x.add_child()
        #         child1.conditions.append(Iff(var, TRUE()))
        #         child2 = x.add_child()
        #         child2.conditions.append(Iff(var, FALSE()))

    def walk_Program(self, node: Program):
        self.walk(node.decls)
        self.walk(node.methods)

    def walk_Load(self, node: Load):
        return self.fp.lookup_or_fresh(node.name, self.table)

    def walk_BinOp(self, node: Comparison):
        op = {
            Token.GE: GE, Token.GT: GT, Token.LE: LE, Token.LT: LT,
            Token.AND: And, Token.OR: Or, Token.IMPL: Implies,
            Token.MUL: mul, Token.ADD: add, Token.SUB: sub}
        left = self.walk(node.left)
        right = self.walk(node.right)
        return op[node.op](left, right)

    def walk_UnaryOp(self, node: UnaryOp):
        op = {Token.NOT: Not}
        expr = self.walk(node.expr)
        return op[node.op](expr)

    def walk_Literal(self, node: Literal):
        return (
            Bool(node.value)
            if isinstance(node.value, bool)
            else Int(node.value))

    def walk_Store(self, node: Store):
        return self.fp.fresh(node.name, self.table)

    def walk_Assign(self, node: Assign):
        rhs = self.walk(node.rhs)
        lhs = self.walk(node.lhs)
        for leaf in self.fp.leaves():
            leaf.assignments[lhs] = rhs

    def _walk_Increment_or_Decrement(self, node, op):
        rhs = self.fp.lookup_or_fresh(node.var_name.name, self.table)
        lhs = self.walk(node.var_name)
        for leaf in self.fp.leaves():
            leaf.assignments[lhs] = op(rhs)

    def walk_Increment(self, node: Increment):
        self._walk_Increment_or_Decrement(node, lambda x: x + 1)

    def walk_Decrement(self, node: Decrement):
        self._walk_Increment_or_Decrement(node, lambda x: x - 1)

    def walk_If(self, node: If):
        or_else = node.or_else or []
        parent_fp = self.fp
        for leaf in self.fp.leaves():
            self.fp = leaf.add_child()
            cond = self.walk(node.cond)
            self.fp.conditions.append(cond)
            self.walk(node.body)

            self.fp = leaf.add_child()
            self.fp.conditions.append(Not(cond))
            self.walk(or_else)
        self.fp = parent_fp

    def walk_MethodDef(self, node: MethodDef):
        self._reset_paths()
        if node.params:
            self.table = self.table.add_child(node.name, is_params=True)
            self.walk(node.params)
        self.fp.conditions.extend(self.walk(n) for n in node.precond)

        self.table = self.table.add_child(node.name)
        self.walk(node.decls)
        self.walk(node.body)

        # self.fp.prune()
        leaves = list(self.fp.leaves(self.fp.get_root()))
        # TODO save these paths somewhere before we reset
        print(node.kind, "method", node.name, "has", len(leaves), "paths")
        input()
        for x in leaves:
            for tr in x.to_transition(self.table):
                print(tr)
        input("[Enter] to scan next method")
        # Move symbol table back to global context
        self.table = self.table.parent


if __name__ == "__main__":
    mbs = ModelBuilderSemantics(types=[
        t for t in globals().values()
        if type(t) is type and issubclass(t, BaseNode)])

    parser: Grammar = compile(GRAMMAR)
    tree = parser.parse(test, semantics=mbs)
    print(tree)

    print("______")
    Walker().walk(tree)
    print("______")
