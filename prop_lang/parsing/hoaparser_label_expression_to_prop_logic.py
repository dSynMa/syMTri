import parsec
from parsec import *

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from prop_lang.value import Value


@generate
def prop_logic_expression():
    yield spaces()
    expr = yield try_choice(boolean_bi_expression, try_choice(unit_prop_logic_expression, bracketed_expression))
    yield spaces()
    return expr


@generate
def unit_prop_logic_expression():
    expr = yield try_choice(boolean_val, try_choice(variable, try_choice(uni_expression, bracketed_expression)))
    yield spaces()
    return expr


@generate
def bracketed_expression():
    yield string("(") << spaces()
    expr = yield prop_logic_expression << spaces()
    yield string(")") << spaces()
    return expr


@generate
def uni_expression():
    op = yield regex("!") << spaces()
    right = yield unit_prop_logic_expression << spaces()
    return UniOp(op, right)


@generate
def boolean_bi_expression():
    op = yield regex("(&+|\\|+|=+|!=|\\-+>|<\\-+>)") << spaces()
    args = yield parsec.sepBy(unit_prop_logic_expression << spaces(), spaces())
    formula = None
    for arg in args:
        if formula == None:
            formula = arg
        else:
            formula = BiOp(formula, op, arg)
    return formula


@generate
def variable():
    var = yield string("LabelAtom(proposition=") >> regex("[0-9\_]+") << string(")")
    return Variable(var)


@generate
def variableFromList(vars: [str]):
    var = yield regex("|".join(vars))
    return Variable(var)


@generate
def boolean_val():
    val = yield regex("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)")
    return Value(val)


parser = prop_logic_expression


def hoaparser_label_expression_to_pl(text: str):
    out = (parser << parsec.eof()).parse(text)
    return out
