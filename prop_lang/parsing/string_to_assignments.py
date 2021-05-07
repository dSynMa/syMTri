import parsec
from parsec import *

from prop_lang.biop import BiOp
from prop_lang.parsing.string_to_fol import variable, fol_expression, math_expression


@generate
def assignments():
    expr = yield sepBy(assignment, spaces() >> regex("(,|;)") >> spaces())
    yield spaces()
    yield optional(regex("(,|;)") >> spaces())
    return expr


@generate
def assignment():
    var = yield variable
    yield spaces()
    yield regex(":=")
    yield spaces()
    val = yield try_choice(fol_expression, math_expression)
    return BiOp(var, ":=", val)


parser = assignments


def string_to_assignments(text: str):
    out = (parser << parsec.eof()).parse(text)
    print(out)
