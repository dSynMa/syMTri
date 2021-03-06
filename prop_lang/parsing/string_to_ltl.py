from prop_lang.formula import Formula
from prop_lang.parsing.string_to_fol import *
from prop_lang.uniop import UniOp


@generate
def ltl_expression():
    yield spaces()
    expr = yield try_choice(bi_ltl_expression, unit_ltl_expression)
    yield spaces()
    return expr


@generate
def unit_ltl_expression():
    yield spaces()
    expr = yield try_choice(bracketed_ltl_expression, try_choice(uni_ltl_expression, unit_fol_expression))
    yield spaces()
    return expr


@generate
def bracketed_ltl_expression():
    yield string("(") << spaces()
    expr = yield ltl_expression << spaces()
    yield string(")") << spaces()
    return expr


@generate
def uni_ltl_expression():
    op = yield regex("(G|X|F)") << spaces()
    right = yield unit_ltl_expression << spaces()
    return UniOp(op, right)


@generate
def bi_ltl_expression_once():
    left = yield unit_ltl_expression << spaces()
    op = yield regex("(&+|\|+|=+|\-+>|<\-+>|U|W|R|M)") << spaces()
    right = yield unit_ltl_expression << spaces()
    return BiOp(left, op, right)


@generate
def bi_ltl_expression():
    left = yield unit_ltl_expression << spaces()
    op = yield regex("(&+|\|+|=+|\-+>|<\-+>|U|W|R|M)") << spaces()
    rights = yield try_choice(sepBy(bi_ltl_expression_once, regex(op)), unit_ltl_expression) << spaces()
    right = rights[0]
    i = 1
    while i < len(rights):
        right = BiOp(right, op, rights[i])
        i += 1
    return BiOp(left, op, right)


parser = ltl_expression


def string_to_ltl(text: str) -> Formula:
    out = (parser << parsec.eof()).parse(text)
    return out
