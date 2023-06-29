#!/usr/bin/env python3

from enum import Enum, auto

from tatsu.grammars import Grammar
from tatsu.objectmodel import Node
from tatsu.semantics import ModelBuilderSemantics
from tatsu.tool import compile
from tatsu.walkers import DepthFirstWalker


class Token(Enum):
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"


class BaseNode(Node):
    def unparse(self) -> str:
        return NotImplementedError()


class Store(BaseNode):
    name = None


class Expr(BaseNode):
    pass


class Load(Expr):
    name = None


class BinOp(Expr):
    left = None
    op = None
    right = None

    def __init__(self, ast=None, **attributes):
        super().__init__(ast, **attributes)
        self.op = Token(self.op)


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

method_extern::MethodDef =
    'method' kind:'extern' ~ >signature '{'
    precond:{ assumption }*
    body:method_body
    '}'
    node_type:`method_extern`
    ;

method_intern::MethodDef =
    'method' 'intern' ~ signature '{'
    precond:{ assertion }*
    body:method_body
    '}'
    node_type:`method_intern`
    ;

method_body = { decl | statement }* ;


assumption = node_type:'assume' '(' expr:expression ')' ';' ;
assertion = node_type:'assert' '(' expr:expression ')' ';' ;

statement =
    | node_type:'if' '(' cond:expression ')' body:statement ['else' else:statement]
    | '{' body:{ statement }* '}' node_type:`block`
    | assignment
    ;

assignment::Assign =
    lhs:lhs ':=' rhs:expression ';' ;

lhs::Store = name:identifier ;

expression
    =
    | add_or_sub
    | term
    ;

add_or_sub::BinOp
    =
    | left:expression op:'+' right:term
    | left:expression op:'-' right:term
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
    | true_lit
    | false_lit
    | number
    | var_reference
    ;

var_reference::Load = name:var_name ;

true_lit::bool = 'true' ;

# For false, we use @:() to return None
# so that bool(None) gives us False
false_lit::bool = 'false' ~ @:() ;

var_name = identifier ;

@name
identifier = /\_?[a-zA-Z][a-zA-Z0-9\_]*/;

number::int = /[0-9]+/;
'''

test = """
    bool x := false;
    bool y := true;
    enum foo { bar, baz };

    foo myFoo := baz;

    method extern foo (bool param) {
        // This is a comment
        x := abc;
        int localInteger := 0 ;

        if (x) {
            x := 5*x; y := x * (3 + y) / 2;
        } else {

        }
    }
    method intern bar () {
        x := abc;
        if (x) { } else {
            x := x; y := x;
        }
    }
"""


class PrintWalker(DepthFirstWalker):
    # def walk_Program(self, node):
    #     self.walk(node.decls)
    #     self.walk(node.enums)
    #     self.walk(node.body)
    #     input(":")
    def walk_BaseNode(self, node, *args):
        print(node)

if __name__ == "__main__":
    # parser: Grammar = compile(GRAMMAR, asmodel=True)
    mbs = ModelBuilderSemantics(types=[Decl, Assign, BinOp, Program])

    parser: Grammar = compile(GRAMMAR)
    tree = parser.parse(test, semantics=mbs)
    print(tree)
    # print(tree)

    # print("______")
    # PrintWalker().walk(tree)
    # print("______")
