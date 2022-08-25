import parsec
from parsec import *

from prop_lang.biop import BiOp
from prop_lang.parsing.string_to_prop_logic import variable, prop_logic_expression, math_expression, math_bi_expression, \
    unit_prop_logic_expression, boolean_bi_expression


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
    val = yield try_choice(math_bi_expression, try_choice(boolean_bi_expression, try_choice(unit_prop_logic_expression, math_expression)))
    return BiOp(var, ":=", val)


parser = assignments


def string_to_assignments(text: str):
    try:
        out = (parser << parsec.eof()).parse(text)
    except Exception as exp:
        print(text)
        raise exp
    return out
