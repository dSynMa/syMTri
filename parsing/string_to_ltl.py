from tatsu import parse

from parsing.string_to_prop_logic import *
from prop_lang.uniop import UniOp

GRAMMAR = '''
    @@grammar::LTL


    start = expression $ ;


    expression
        =
        | level_2 '->' expression
        | level_2 '<->' expression
        | level_2
        ;

    level_2
        =
        | level_1 '|' level_2
        | level_1 '||' level_2
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
        | '(' @:expression ')'
        | atomic 'U' atomic
        | atomic 'W' atomic
        | atomic 'R' atomic
        | atomic 'M' atomic
        | term
        ;


    term
        =
        | 'true'
        | 'false'
        | atom
        ;

    atom = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
'''


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)", node):
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        return UniOp(node[0], tuple_to_formula(node[1]))
    elif len(node) == 3:
        return BiOp(tuple_to_formula(node[0]), node[1], tuple_to_formula(node[2]))
    else:
        raise Exception("Invalid node: " + str(node))


def string_to_ltl(text: str) -> Formula:
    ast = parse(GRAMMAR, text)
    formula = tuple_to_formula(ast)
    return formula
