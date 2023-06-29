#!/usr/bin/env python3

from copy import deepcopy
from dataclasses import dataclass
from enum import Enum, auto
from itertools import product
from operator import add, mul, sub
from typing import Any

from pysmt.shortcuts import (GE, GT, LE, LT, And, Bool, Equals, FreshSymbol,
                             Iff, Int, Not, Or, get_type, simplify)
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


class BinOp(Expr):
    left = None
    op = None
    right = None

    def __init__(self, ast=None, **attributes):
        super().__init__(ast, **attributes)
        self.op = Token(self.op)


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
parameter =
    typ:identifier name:identifier
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
    | bool_lit
    | number_lit
    | var_reference
    ;

var_reference::Load = name:var_name ;

var_name = identifier ;

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

test = """
    bool x := false;
    bool y := true;
    int z := 0;
    //enum foo { bar, baz };
    //foo myFoo := baz;

    method extern foo (bool param) {
        // This is a comment
        assume(z > 1 && z < 4);
        int localInteger := 0 ;
        z := 2*z;

        if (z > 10) {
            z := 5*z; y := z > 4;
        } else {

        }

        z := z+1;
    }
    method intern bar () {
        x := true;
        if (x) {
            if (z>10) z := z + 1;
        } else {
            x := x; y := x;
        }
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
            raise KeyError(f"Symbol {name} not found")
        else:
            return self.parent.lookup(name)

    def add(self, name, init, type_):
        builtin_types = {'int': INT, 'bool': BOOL}
        symbol = SymbolTableEntry(name, self, init, builtin_types[type_])
        self.symbols[name] = symbol


class Path:
    def __init__(self, copy_from: 'Path' = None) -> None:
        if copy_from is not None:
            self.variables = {**copy_from.variables}
            self.prefix = {*copy_from.prefix}
        self.variables = {}
        self.prefix = []

    def __str__(self) -> str:
        return f"{self.prefix}({self.variables})"

    def __repr__(self) -> str:
        return f"{self.prefix}({self.variables})"

    def fresh(self, name, table):
        symbol = table.lookup(name)
        self.variables[name] = FreshSymbol(symbol.type_, name + "!%d")
        return self.variables[name]

    def lookup_or_fresh(self, name, table):
        if name in self.variables:
            return self.variables[name]
        return self.fresh(name, table)


class Walker(NodeWalker):
    # def walk_Program(self, node):
    #     self.walk(node.decls)
    #     self.walk(node.enums)
    #     self.walk(node.body)
    #     input(":")

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
        self.table.add(node.var_name, node.init, node.var_type)

    def walk_Program(self, node: Program):
        
        for n in node.decls:
            self.walk(n)

        for n in node.methods:
            self.walk(n)

    def walk_Load(self, node: Load):
        return self.cur_path.lookup_or_fresh(node.name, self.table)


    def walk_BinOp(self, node: Comparison):
        op = {
            Token.GT: GT, Token.LE: LE, Token.LT: LT,
            Token.AND: And, Token.OR: Or,
            Token.MUL: mul, Token.ADD: add
        }
        left = self.walk(node.left)
        right = self.walk(node.right)
        return op[node.op](left, right)

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
            p.prefix.append(op(lhs, rhs))

    def walk_If(self, node: If):
        body = [node.body] if not isinstance(node.body, list) else node.body
        if node.or_else is not None:
            snap_before = deepcopy(self.all_paths)
        for p in self.all_paths:
            self.cur_path = p
            cond = self.walk(node.cond)
            p.prefix.append(cond)
        for p, n in product(self.all_paths, body):
            self.cur_path = p
            self.walk(n)

        if node.or_else is not None:
            or_else = [node.or_else] if not isinstance(node.or_else, list) else node.or_else  # noqa: E501
            snap_after = deepcopy(self.all_paths)
            self.all_paths = snap_before
            for p in self.all_paths:
                self.cur_path = p
                cond = self.walk(node.cond)
                p.prefix.append(Not(cond))
            for p, n in product(self.all_paths, or_else):
                self.cur_path = p
                self.walk(n)
            self.all_paths.extend(snap_after)

    def walk_MethodDef(self, node: MethodDef):
        self._reset_paths()
        self.table = self.table.add_child(node.name)
        print(node.name, node.kind)
        for n in node.decls:
            self.walk(n)
        self.cur_path.prefix.extend(self.walk(n) for n in node.precond)

        for n in node.body:
            self.walk(n)
        for p in self.all_paths:
            print(p)
            print(simplify(And(p.prefix)))
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

