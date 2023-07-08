#!/usr/bin/env python3

from collections import Counter, defaultdict, deque
from copy import deepcopy
from dataclasses import dataclass
from enum import Enum
from itertools import chain, combinations
from operator import add, mul, sub

from pysmt.fnode import FNode
from pysmt.shortcuts import (FALSE, GE, GT, LE, LT, And, Bool, EqualsOrIff,
                             Implies, Int, Not, NotEquals, Or, Symbol,
                             get_free_variables, get_type, simplify,
                             substitute, is_sat)
from pysmt.typing import BOOL, INT
from tatsu.grammars import Grammar
from tatsu.objectmodel import Node
from tatsu.semantics import ModelBuilderSemantics
from tatsu.tool import compile
from tatsu.walkers import NodeWalker

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


def remove_version(var):
    return Symbol(var.symbol_name().split("#")[0], get_type(var))


def remove_all_versions(formula):
    fvs = get_free_variables(formula)
    return substitute(formula, {fv: remove_version(fv) for fv in fvs})


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
    NE      = "!="
    AND     = "&&"
    OR      = "||"
    IMPL    = "=>"
    NOT     = "!"


class BaseNode(Node):
    def unparse(self) -> str:
        raise NotImplementedError()


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
    left: Expr = None
    op = None
    right: Expr = None




class Increment(BaseNode):
    var_name = None


class Decrement(BaseNode):
    var_name = None


class UnaryOp(Operation):
    op = None
    expr: Expr = None


class Comparison(BinOp):
    pass


class BinLogic(BinOp):
    pass


class If(BaseNode):
    cond = None
    body = None
    or_else = None


class Assign(BaseNode):
    lhs: Store = None
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
    assumes = None
    asserts = None
    decls = None
    body = None


class Program(BaseNode):
    decls = None
    enums = None
    methods = None


def to_formula(expr: FNode):
    tests_biop = {
        "+": expr.is_plus,
        "-": expr.is_minus,
        "*": expr.is_times,
        "/": expr.is_div,
        "<=": expr.is_le,
        "<": expr.is_lt,
        "==": expr.is_equals,
        "<=>": expr.is_iff,
        "=>": expr.is_implies,
        "&&": expr.is_and,
        "||": expr.is_or,
    }

    for op, test in tests_biop.items():
        if test():
            new_expr = None
            for arg in expr.args():
                if new_expr is None:
                    new_expr = to_formula(arg)
                    continue
                new_expr = BiOp(new_expr, op, to_formula(arg))
            return new_expr

    if expr.is_constant():
        return Value(str(expr))

    if expr.is_symbol():
        return Variable(expr.symbol_name())
    elif expr.is_not():
        return UniOp("!", to_formula(expr.arg(0)))

    # We've tried so hard & got so far
    raise NotImplementedError(expr, expr.node_type())


GRAMMAR = '''
@@grammar::POPL
@@keyword :: assert assume else enum extern false if intern method true
@@eol_comments :: /\/\/.*?$/


start::Program =
    { decls+:global_decl | enums+:enum_def }*
    methods:{ method }+
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

method::MethodDef =
    'method' kind:( 'extern' | 'intern' ) ~ >signature '{'
    { assumes+:assumption | asserts+:assertion }*
    decls: { decl }*
    body:{ statement }*
    '}'
    node_type:`method_extern`
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

@dataclass
class SymbolTableEntry:
    name: str
    context: 'SymbolTable'
    init: any
    type_: any      # SMT type of the variable
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

    def __iter__(self):
        yield from self.symbols.values()
        for child in self.children:
            yield from child

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
            raise KeyError(f"Symbol {name} not found in {self}")
        else:
            return self.parent.lookup(name)

    def add(self, node: Decl, init) -> SymbolTableEntry:
        builtin_types = {'int': INT, 'bool': BOOL}
        symbol = SymbolTableEntry(
            node.var_name, self, init, builtin_types[node.var_type], node)
        self.symbols[node.var_name] = symbol
        return symbol


class ForkingPath:
    def __init__(self, parent=None, table=None) -> None:
        self.variables = {}
        self.counters = Counter() if parent is None else deepcopy(parent.counters)  # noqa: E501
        self.assignments = {}
        # self.assignments = []
        self.conditions = []
        self.children = []
        self.table = table or (SymbolTable() if parent is None else parent.table)
        self.parent = parent

    def _lookup(self, name):
        if name in self.variables:
            return self.variables[name]
        return None if self.parent is None else self.parent._lookup(name)

    def fresh(self, name):
        symbol = self.table.lookup(name)
        self.variables[name] = Symbol(f"{name}#{self.counters[name]}", symbol.type_)  # noqa: E501
        self.counters[name] += 1
        return self.variables[name]

    def lookup_or_fresh(self, name):
        return self._lookup(name) or self.fresh(name)

    def add_child(self, table=None):
        child = ForkingPath(self, table)
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

    def to_transitions(self):
        table = self.table
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


class SymexWalker(NodeWalker):

    def __init__(self):
        super().__init__()
        self.paths = {}
        self.fp = ForkingPath()

        self.extern_assumes = set()
        self.extern_asserts = {}
        self.intern_assumes = set()
        self.intern_asserts = {}

        self.extern_triples = defaultdict(list)
        self.intern_triples = defaultdict(list)


    def push(self, frame):
        self.ctx.append(frame)

    def pop(self):
        return self.ctx.pop()

    def context(self):
        return self.ctx[-1]

    def walk_Decl(self, node: Decl):
        init = self.walk(node.init)
        self.fp.table.add(node, init)
        if self.fp.table.parent is not None and node.init is not None:
            var = self.fp.fresh(node.var_name)
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

        self.env_choices = {
            name: Symbol(f"__{name}") for name in self.extern_triples}
        self.con_choices = {
            name: Symbol(f"__{name}") for name in self.intern_triples}

        # Post-processing: add booleans to represent chosen methods
        def add_choice_booleans(triples_dict, booleans_dict):
            for name, triples in triples_dict.items():
                for x in triples:
                    x[0].extend(self.one_hot(name, booleans_dict))
        add_choice_booleans(self.extern_triples, self.env_choices)
        add_choice_booleans(self.intern_triples, self.con_choices)

    def one_hot(self, name, booleans_dict):
        result = [Not(var) if var_name != name else var
                  for var_name, var in booleans_dict.items()]
        return result

    def walk_Load(self, node: Load):
        return self.fp.lookup_or_fresh(node.name)

    def walk_BinOp(self, node: Comparison):
        op = {
            Token.EQ: EqualsOrIff, Token.NE: NotEquals,
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
        return self.fp.fresh(node.name)

    def walk_Assign(self, node: Assign):
        rhs = self.walk(node.rhs)
        lhs = self.walk(node.lhs)
        for leaf in self.fp.leaves():
            leaf.assignments[lhs] = rhs

    def _walk_Increment_or_Decrement(self, node, op):
        rhs = self.fp.lookup_or_fresh(node.var_name.name)
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
        self.fp = self.fp.add_child(
            self.fp.table.add_child(node.name, is_params=node.params))
        if node.params:
            self.walk(node.params)
        assumes = [self.walk(n) for n in node.assumes or []]
        asserts = [self.walk(n) for n in node.asserts or []]

        if node.kind == "intern":
            self.intern_asserts[node.name] = [remove_all_versions(x) for x in asserts]
            self.intern_asserts[node.name].extend(remove_all_versions(x) for x in assumes)
        else:
            self.extern_asserts[node.name] = [remove_all_versions(x) for x in asserts]
            self.extern_asserts[node.name].extend(remove_all_versions(x) for x in assumes)

        self.fp.conditions.extend(assumes)
        self.fp.conditions.extend(asserts)

        if node.params:
            self.fp.table = self.fp.table.add_child(node.name)

        self.walk(node.decls)
        self.walk(node.body)

        self.paths[node.name] = self.fp 
        while self.fp.parent is not None:
            self.fp = self.fp.parent

        # self.fp.prune()
        for x in self.paths[node.name].leaves():
            if node.kind == "extern":
                self.extern_triples[node.name].extend(x.to_transitions())
            else:
                self.intern_triples[node.name].extend(x.to_transitions())


dsl_parser: Grammar = compile(GRAMMAR)

__semantics = ModelBuilderSemantics(types=[
        t for t in globals().values()
        if type(t) is type and issubclass(t, BaseNode)])


def parse_dsl(code: str) -> BaseNode:
    return dsl_parser.parse(code, semantics=__semantics)


if __name__ == "__main__":
    with open("/Users/lucad/git/syMTri/examples/dsl/rev_lane.dsl") as f:
        code = f.read()
    tree = parse_dsl(code)
    wlk = SymexWalker()
    wlk.walk(tree)

