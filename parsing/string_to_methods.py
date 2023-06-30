#!/usr/bin/env python3

from collections import Counter
from copy import deepcopy
from dataclasses import dataclass
from enum import Enum, auto
from itertools import product
from operator import add, mul, sub
from typing import Any

from pysmt.shortcuts import (GE, GT, LE, LT, And, Bool, Equals, Symbol, FALSE, TRUE,
                             Iff, Int, Not, Or, get_type, simplify, Implies)
from pysmt.typing import BOOL, INT
from tatsu.grammars import Grammar
from tatsu.objectmodel import Node
from tatsu.semantics import ModelBuilderSemantics
from tatsu.tool import compile
from tatsu.walkers import NodeWalker


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
    { decls+:decl | enums+:enum_def }*
    methods:{ method_extern | method_intern }+
    $
    ;

enum_def::EnumDef =
    'enum' ~ name:identifier '{'  values:','.{identifier}+ '}' ';'
    ;

decl::Decl =
    var_type:identifier var_name:identifier ':=' init:expression ';'
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
    ;



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

var_reference::Load = name:store ;

store = identifier ;

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
    bool danger := false;
    bool closed_from_left := true;
    bool closed_from_right := true;
    bool change_direction := false;

    method extern sensor_update(bool car_from_left_entry, bool car_from_right_entry,
                                  bool car_from_left_exit, bool car_from_right_exit,
                                  bool _change_direction){
        assume(closed_from_left => !car_from_left_entry);
        assume(closed_from_right => !car_from_right_entry);

        if (car_from_left_entry) cars_from_left := cars_from_left+1;

        if (car_from_right_entry) cars_from_right := cars_from_right+1;

        if (car_from_left_exit) cars_from_left := cars_from_left - 1;

        if (car_from_right_exit) cars_from_right := cars_from_right - 1;

        change_direction := _change_direction;

        danger := cars_from_left > 0 && cars_from_right > 0;
    }

    method intern control(bool close_from_left, bool close_from_right){
        int pippo := 3;
        closed_from_left := close_from_left;
        closed_from_right := close_from_right;
    }
"""


@dataclass
class SymbolTableEntry:
    name: str
    context: str
    init: any
    type_: any


class SymbolTable:
    def __init__(self, name="<global>", parent=None):
        self.name = name
        self.parent = parent
        self.children = []
        self.symbols = {}

    def __getitem__(self, key):
        return self.symbols[key]

    def __contains__(self, key):
        return key in self.symbols

    def __str__(self) -> str:
        return f"{self.name}:{self.symbols}"

    def add_child(self, name):
        table = SymbolTable(name, parent=self)
        self.children.append(table)
        return table

    def lookup(self, name) -> SymbolTableEntry:
        if name in self.symbols:
            return self.symbols[name]
        elif self.parent is None:
            print(self)
            raise KeyError(f"Symbol {name} not found")
        else:
            return self.parent.lookup(name)

    def add(self, name, init, type_) -> SymbolTableEntry:
        builtin_types = {'int': INT, 'bool': BOOL}
        symbol = SymbolTableEntry(name, self, init, builtin_types[type_])
        self.symbols[name] = symbol
        return symbol


class Path:
    def __init__(self) -> None:
        self.variables = {}
        self.counters = Counter()
        self.assignments = []
        self.conditions = []

    def __str__(self) -> str:
        return f"{self.conditions}-->{self.assignments}({self.variables})"

    def __repr__(self) -> str:
        return f"{self.prefix}({self.variables})"

    def fresh(self, name, table):
        symbol = table.lookup(name)
        self.counters[name] += 1
        self.variables[name] = Symbol(f"{name}#{self.counters[name]}", symbol.type_)  # noqa: E501
        return self.variables[name]

    def lookup_or_fresh(self, name, table):
        if name in self.variables:
            return self.variables[name]
        return self.fresh(name, table)


class Walker(NodeWalker):

    def __init__(self):
        super().__init__()
        self._reset_paths()
        self.table = SymbolTable()
        self.symbols = {}

    def _reset_paths(self):
        root_path = Path()
        self.cur_path = root_path
        self.all_paths = [root_path]

    def push(self, frame):
        self.ctx.append(frame)

    def pop(self):
        return self.ctx.pop()

    def context(self):
        return self.ctx[-1]

    def walk_Decl(self, node: Decl):
        init = self.walk(node.init)
        symbol = self.table.add(node.var_name, init, node.var_type)
        if self.table.parent is not None and node.init is not None:
            # Local variable
            op = Iff if symbol.type_ == BOOL else Equals
            for p in self.all_paths:
                var = p.fresh(node.var_name, self.table)
                p.assignments.append(op(var, init))
        elif "##params" in self.table.name:
            # This is a parameter
            snap_paths = deepcopy(self.all_paths)
            for p in self.all_paths:
                var = p.fresh(node.var_name, self.table)
                p.conditions.append(Iff(var, TRUE()))
            for p in snap_paths:
                var = p.fresh(node.var_name, self.table)
                p.conditions.append(Iff(var, FALSE()))
            self.all_paths.extend(snap_paths)

    def walk_Program(self, node: Program):
        self.walk(node.decls)
        self.walk(node.methods)

    def walk_Load(self, node: Load):
        return self.cur_path.lookup_or_fresh(node.name, self.table)

    def walk_BinOp(self, node: Comparison):
        op = {
            Token.GT: GT, Token.LE: LE, Token.LT: LT,
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

    def walk_Store(self, node:Store):
        return self.cur_path.fresh(node.name, self.table)

    def walk_Assign(self, node: Assign):
        for p in self.all_paths:
            self.cur_path = p
            rhs = self.walk(node.rhs)
            lhs = self.walk(node.lhs)
            op = Iff if get_type(lhs) == BOOL else Equals
            p.assignments.append(op(lhs, rhs))

    def walk_If(self, node: If):
        or_else = node.or_else or []
        snap_before = deepcopy(self.all_paths)
        for p in self.all_paths:
            self.cur_path = p
            cond = self.walk(node.cond)
            p.conditions.append(cond)

        self.walk(node.body)

        snap_after = deepcopy(self.all_paths)
        self.all_paths = snap_before
        for p in self.all_paths:
            self.cur_path = p
            cond = self.walk(node.cond)
            p.conditions.append(Not(cond))

        self.walk(or_else)
        self.all_paths.extend(snap_after)

    def walk_MethodDef(self, node: MethodDef):
        self._reset_paths()
        if node.params:
            self.table = self.table.add_child(node.name + "##params")
            self.walk(node.params)
        for p in self.all_paths:
            self.cur_path = p
            p.conditions.extend(self.walk(n) for n in node.precond)
        self.all_paths = [
            p for p in self.all_paths
            if simplify(And(p.conditions)) != FALSE()
        ]

        self.table = self.table.add_child(node.name)
        # for n in node.decls:
        self.walk(node.decls)
        self.walk(node.body)

        self.all_paths = [
            p for p in self.all_paths
            if simplify(And(And(p.conditions), And(p.assignments))) != FALSE()
        ]
        print(node.name, node.kind, len(self.all_paths))
        input()
        for p in self.all_paths:
            # cond = simplify(And(p.conditions))
            cond = simplify(And(And(p.conditions), And(p.assignments)))
            if cond != FALSE():
                print(p)
                print()

            # TODO save the paths somewhere before we reset
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
