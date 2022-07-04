import parsec
from parsec import *

from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from prop_lang.value import Value


@generate
def prop_logic_expression():
    yield spaces()
    expr = yield try_choice(boolean_bi_expression, unit_prop_logic_expression)
    yield spaces()
    return expr


@generate
def unit_prop_logic_expression():
    expr = yield try_choice(boolean_math_bi_expression, try_choice(variable, try_choice(boolean_val, try_choice(uni_expression,
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
    op = yield regex("(&+|\\|+|=+|!=|\\-+>|<\\-+>)") << spaces()
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
    left = yield math_expression << spaces()
    op = yield regex("(\\+|\\-|%|\\*|\\/)") << spaces()
    right = yield math_expression << spaces()
    return MathExpr(BiOp(left, op, right))


@generate
def variable():
    var = yield regex("[a-zA-Z]+")
    return Variable(var)


@generate
def variableFromList(vars: [str]):
    var = yield regex("|".join(vars))
    return Variable(var)


@generate
def number_val():
    val = yield regex("[0-9]+(\\.[0-9]+)?")
    return Value(val)


@generate
def math_expression():
    return MathExpr((yield try_choice(number_val, variable)))


@generate
def math_bracketed_expression():
    yield string("(") << spaces()
    expr = math_expression
    yield string(")") << spaces()
    return expr


@generate
def boolean_val():
    val = yield regex("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)")
    return Value(val)


parser = prop_logic_expression


def string_to_fol(text: str):
    out = (parser << parsec.eof()).parse(text)
    print(out)
