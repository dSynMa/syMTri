import re

from parsec import *
from tatsu.grammars import Grammar
from tatsu.infos import ParserConfig
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable

GRAMMAR = '''
    @@grammar::PROPLOGIC


    start = expression $ ;

    expression
        =
        | level_2 '->' expression
        | level_2 '<->' expression
        | level_2
        ;
    
    level_2
        =
        | level_1 '||' level_2
        | level_1 '|' level_2
        | level_1
        | atomic
        ;
    
    level_1 
        =
        | atomic '&&' level_1
        | atomic '&' level_1
        | atomic
        ;
    
    atomic
        =
        | '!' atomic
        | 'X' atomic
        | 'F' atomic
        | 'G' atomic
        | '(' expression ')'
        | atomic 'U' atomic
        | atomic 'W' atomic
        | atomic 'R' atomic
        | atomic 'M' atomic
        | math_expression '<' math_expression
        | math_expression '<=' math_expression
        | math_expression '>' math_expression
        | math_expression '>=' math_expression
        | math_expression '==' math_expression
        | math_expression '!=' math_expression
        | term
        ;


    term
        =
        | 'true'
        | 'false'
        | atom
        ;
        
    math_expression
        = math_1 '*' math_expression
        | math_1 '/' math_expression
        | math_1
        ;
        
    math_expression_eof
        = math_expression $ ;
    
    math_1
        = math_0 '+' math_1
        | math_0 '-' math_1
        | math_0
        ;
    
    math_0
        = '(' math_expression ')'
        | number
        | atom
        ;

    atom = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
    number = /\d+|\d+\.\d+/;
'''

parser: Grammar = compile(GRAMMAR)
math_config = ParserConfig(start='math_expression_eof')


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)|[0-9]+(\.[0-9]+)?", node):
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        return UniOp(node[0], tuple_to_formula(node[1]))
    elif len(node) == 3:
        if node[0] == "(":
            return tuple_to_formula(node[1])
        else:
            v0 = (tuple_to_formula(node[0]))
            v2 = (tuple_to_formula(node[2]))
            if v0 == None or v2 == None:
                print("None")
            if re.match("(\+|\-|\*|\/|<|>|<=|>=|==)", node[1]):
                return MathExpr(BiOp(tuple_to_formula(node[0]), node[1], tuple_to_formula(node[2])))
            else:
                return BiOp(tuple_to_formula(node[0]), node[1], tuple_to_formula(node[2]))
    else:
        raise Exception("Invalid node: " + str(node))


def string_to_math_expression(text: str) -> MathExpr:
    ast = parser.parse(text, config=math_config)
    formula = tuple_to_formula(ast)
    return formula


def string_to_prop(text: str) -> Formula:
    ast = parser.parse(text)
    formula = tuple_to_formula(ast)
    return formula
