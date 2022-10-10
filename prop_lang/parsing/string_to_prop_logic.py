import parsec
from parsec import *

from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


@generate
def prop_logic_expression():
    yield spaces()
    expr = yield try_choice(boolean_bi_expression, try_choice(unit_prop_logic_expression, bracketed_expression))
    yield spaces()
    return expr


@generate
def unit_prop_logic_expression():
    expr = yield try_choice(uni_expression,
                            try_choice(boolean_math_bi_expression, try_choice(boolean_val, try_choice(variable,
                                                                                                      bracketed_expression))))
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
    left = yield unit_prop_logic_expression << spaces()
    op = yield regex("(&+|\|+|=+|!=|\\-+>|<\\-+>)") << spaces()
    right = yield unit_prop_logic_expression << spaces()
    return BiOp(left, op, right)


@generate
def boolean_math_bi_expression():
    left = yield try_choice(math_bi_expression, math_expression) << spaces()
    op = yield regex("(!=|=+|>=|<=|>|<)") << spaces()
    right = yield try_choice(math_bi_expression, math_expression) << spaces()
    return MathExpr(BiOp(left, op, right))


@generate
def math_bi_expression():
    left = yield math_unit_expression << spaces()
    op = yield regex("(\\+|\\-|%|\\*|\\/)") << spaces()
    right = yield math_unit_expression << spaces()
    return MathExpr(BiOp(left, op, right))


@generate
def math_uni_expression():
    op = yield regex("\\-") << spaces()
    right = yield math_unit_expression << spaces()
    return MathExpr(UniOp(op, right))


@generate
def number_val():
    val = yield regex("[0-9]+(\\.[0-9]+)?")
    return Value(val)


@generate
def math_basic_expression():
    return MathExpr((yield try_choice(number_val, variable)))


@generate
def math_bracketed_expression():
    yield string("(") << spaces()
    expr = math_expression
    yield string(")") << spaces()
    return expr


@generate
def math_expression():
    yield spaces()
    expr = yield try_choice(try_choice(math_bi_expression,
                                       math_unit_expression), math_bracketed_expression)
    yield spaces()
    return expr


@generate
def math_unit_expression():
    expr = yield try_choice(number_val, try_choice(variable,
                                                   try_choice(math_uni_expression, math_bracketed_expression)))
    yield spaces()
    return expr


@generate
def variable():
    var = yield regex("\_?[a-zA-Z][a-zA-Z0-9\_\-]*")
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

math_parser = math_expression


def string_to_pl(text: str):
    out = (parser << parsec.eof()).parse(text)
    return out


def string_to_mathexpr(text: str):
    out = (math_parser << parsec.eof()).parse(text)
    return out
