from typing import Tuple

import ply.yacc as yacc
from pip._vendor.distlib.compat import raw_input
from ply import lex

from monitors.monitor import Monitor
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp

tokens = (
    'NUMBER',
    'INPUTS',
    'OUTPUTS',
    'NUM_INPUT',
    'NUM_OUTPUT',
    'NUM_PRODUCTS',
    'NUM_STATES',
    'NUM_RESET_STATE',
    'STATE',
    'PLUS'
)

# Regular expression rules for simple tokens
t_INPUTS = r'\.inputs'
t_OUTPUTS = r'\.outputs'
t_NUM_INPUT = r'\.i'
t_NUM_OUTPUT = r'\.o'
t_NUM_PRODUCTS = r'\.p'
t_NUM_STATES = r'\.s'
t_NUM_RESET_STATE = r'\.r'
t_PLUS = r'\+'


# # A regular expression rule with some action code
def t_NUMBER(t):
    r'[0-9-]+'
    return t


def t_STATE(t):
    r'[a-zA-Z_0-9*-]+'
    return t


def t_NEWLINE(t):
    r'\n+'
    return t


# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t\n'


# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
lexer = lex.lex(errorlog=yacc.NullLogger())


# TODO use these for sanity checking
class vars:
    inputs = []
    outputs = []
    input_no = 0
    output_no = 0
    products_no = 0
    states_no = 0
    reset_state = ""
    end_state = "end"
    in_act: [Atom]
    out_act: [Atom]
    end_act: Atom


# .inputs req0 req1 .outputs grant0 grant1 .i 2 .o 2 .p 2 .s 2 .r S0 -- S0 S1 10 -- S1 S0 01
#
def p_kiss(p):
    'expression : inputs_st outputs_st inputs outputs products states reset transitions'
    name = ""
    p[0] = Monitor(name,
                   [],
                   p[7],
                   [],
                   [],
                   [],
                   [str(i) for i in vars.in_act],
                   [str(o) for o in vars.out_act]
                   )
    for t in p[8]:
        p[0].add_transition(t[0], t[1], t[2], t[3], t[4])

    p[0].flag_states = [vars.end_state]


def p_expression_inputs(p):
    'inputs_st : INPUTS istatelist'
    vars.inputs = p[2]


def p_expression_outputs(p):
    'outputs_st : OUTPUTS ostatelist'
    vars.outputs = p[2]


def p_expression_istatelist(p):
    'istatelist : istate'


def p_expression_istatelist_mult(p):
    'istatelist : istate istatelist'


def p_expression_istate(p):
    'istate : STATE'
    vars.inputs.append(p[1])


def p_expression_ostatelist(p):
    'ostatelist : ostate'


def p_expression_ostatelist_mult(p):
    'ostatelist : ostate ostatelist'


def p_expression_ostate(p):
    'ostate : STATE'
    vars.outputs.append(p[1])


def p_expression_num_inputs(p):
    'inputs : NUM_INPUT NUMBER'
    vars.input_no = p[2]


def p_expression_num_outputs(p):
    'outputs : NUM_OUTPUT NUMBER'
    vars.output_no = p[2]


def p_expression_products(p):
    'products : NUM_PRODUCTS NUMBER'
    vars.products_no = p[2]


def p_expression_states(p):
    'states : NUM_STATES NUMBER'
    vars.states_no = int(p[2])


def p_expression_reset(p):
    'reset : NUM_RESET_STATE STATE'
    p[0] = p[2]


def p_expression_transitions_1(p):
    'transitions : transition'
    p[0] = [p[1]]


def p_expression_transitions_more(p):
    'transitions : transition transitions'
    p[0] = [p[1]] + p[2]


def p_expression_transition(p):
    'transition : acts STATE STATE acts'
    ins = map(lambda x: kiss_events_to_date_events(True, x), p[1])
    outs = map(lambda x: kiss_events_to_date_events(False, x), p[4])
    p[0] = []
    for (_, input) in ins:
        for (is_end_trans, output) in outs:
            p[0] += [p[2],
                     input,
                     [],
                     output,
                     vars.end_state if is_end_trans else p[3]]


def p_acts(p):
    '''acts : number
             | numbers '''
    p[0] = p[1]


def p_number(p):
    '''number : NUMBER'''
    p[0] = [p[1]]


def p_numbers_1(p):
    '''numbers : number'''
    p[0] = [p[1]]


def p_numbers(p):
    '''numbers : number PLUS numbers'''
    p[0] = p[1] + p[3]


def kiss_events_to_date_events(inputs: bool, kiss_events: str) -> Tuple[bool, Formula]:
    notreq = []
    req = []
    i = 0
    while i < len(kiss_events):
        if kiss_events[i] != "-":
            event = vars.in_act[i] if inputs else vars.out_act[i]
            if kiss_events[i] == "0":
                notreq.append(event)
            else:
                req.append(event)
        i = i + 1
    atom = None
    if len(notreq) > 0:
        for a in notreq:
            if atom is None:
                atom = UniOp("!", a)
            else:
                atom = BiOp(atom, "&", UniOp("!", a))

    if len(req) > 0:
        for a in notreq:
            if atom is None:
                atom = Atom(a)
            else:
                atom = BiOp(atom, "&", Atom(a))

    if vars.end_act is not None:
        if vars.end_act in req:
            return True, vars.end_act

    return False, atom


class error:
    text: str


# Error rule for syntax errors
def p_error(p):
    print("Syntax error caused by token " + str(p) + " when trying to parse Strix (KISS) output " + error.text.replace(
        "\n", ""))
    raise SystemExit(0)


# Build the parser
parser = yacc.yacc(errorlog=yacc.NullLogger())


def interactive_parser():
    while True:
        try:
            s = raw_input('calc > ')
        except EOFError:
            break
        if not s: continue
        result = parser.parse(s, lexer=lexer)
        print(result)


def kiss_to_monitor(text: str, in_act: [Atom], out_act: [Atom], end_act: Atom) -> Monitor:
    error.text = text
    vars.in_act = in_act
    vars.out_act = out_act
    vars.end_act = end_act
    dt = parser.parse(text)
    dt.reduce()
    return dt


if __name__ == "__main__":
    interactive_parser()
