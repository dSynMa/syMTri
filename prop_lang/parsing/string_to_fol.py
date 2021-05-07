import parsec
from parsec import *

from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp


@generate
def fol_expression():
    yield spaces()
    expr = yield try_choice(boolean_bi_expression, unit_fol_expression)
    yield spaces()
    return expr


@generate
def unit_fol_expression():
    expr = yield try_choice(math_bi_expression, try_choice(variable, try_choice(boolean_val, try_choice(uni_expression,
                                                                                                        bracketed_expression))))
    yield spaces()
    return expr


@generate
def bracketed_expression():
    yield string("(") << spaces()
    expr = yield fol_expression << spaces()
    yield string(")") << spaces()
    return expr


@generate
def uni_expression():
    op = yield regex("!") << spaces()
    right = yield unit_fol_expression << spaces()
    return UniOp(op, right)


@generate
def boolean_bi_expression():
    left = yield unit_fol_expression << spaces()
    op = yield regex("(&+|\|+|=+|\-+>|<\-+>)") << spaces()
    right = yield unit_fol_expression << spaces()
    return BiOp(left, op, right)


@generate
def math_bi_expression():
    left = yield math_expression << spaces()
    op = yield regex("(\+|%|\*|\/|=|>=|<=|>|<)") << spaces()
    right = yield math_expression << spaces()
    return BiOp(left, op, right)


@generate
def variable():
    var = yield regex("[a-zA-Z]+")
    return Atom(var)


@generate
def number_val():
    val = yield regex("[0-9]+(\.[0-9]+)?")
    return Atom(val)


@generate
def math_expression():
    var = yield try_choice(number_val, variable)
    return Atom(var)


@generate
def math_bracketed_expression():
    yield string("(") << spaces()
    expr = math_expression
    yield string(")") << spaces()
    return expr


@generate
def boolean_val():
    val = yield regex("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)")
    return Atom(val)


parser = fol_expression


def string_to_fol(text: str):
    out = (parser << parsec.eof()).parse(text)
    print(out)
