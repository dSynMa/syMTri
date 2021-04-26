import ply.yacc as yacc

from pip._vendor.distlib.compat import raw_input
from ply import lex

from monitors.monitor import Monitor
from prop_lang.atom import Atom
from prop_lang.assignments.string_to_assignments import string_to_assignments
from prop_lang.fol.string_to_fol import string_to_fol

tokens = (
    'Monitor',
    'STATES',
    'TRANSITIONS',
    'INITIAL',
    'FLAGGING',
    'LPAREN',
    'RPAREN',
    # 'LSQPAREN',
    # 'RSQPAREN',
    'COMMA',
    'EQUALS',
    'ARROW',
    'CONDACTDELIM',
    'CONDACT',
    'NAME',
    'VALUATION'
)


def t_COMMA(t):
    r'(,|;)'
    return t


def t_LPAREN(t):
    r'{'
    return t


def t_RPAREN(t):
    r'}'
    return t


def t_Monitor(t):
    r'monitor'
    return t


def t_STATES(t):
    r'STATES'
    return t


def t_TRANSITIONS(t):
    r'TRANSITIONS'
    return t


def t_INITIAL(t):
    r'INITIAL'
    return t


def t_FLAGGING(t):
    r'FLAGGING'
    return t


def t_VALUATION(t):
    r'VALUATION'
    return t


def t_ARROW(t):
    r'->'
    return t


def t_CONDACTDELIM(t):
    r'>>'
    return t


# # A regular expression rule with some action code
def t_NAME(t):
    r'[a-zA-Z0-9&*:|%.!$^><+_=\\-]+'
    return t


# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t\n'


# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
lexer = lex.lex(errorlog=yacc.NullLogger())


def p_expression_Monitors(p):
    'expression : Monitor NAME LPAREN states init init_val flaggingstates transitions RPAREN'
    transitions = []
    init_val = string_to_assignments(";".join(p[6]))
    p[0] = Monitor(p[2], p[4], p[5], init_val, p[7], [])
    for t in p[8]:
        p[0].add_transition(t[0], t[1], t[2], Atom("true"), t[3])


def p_expression_init(p):
    'init : INITIAL LPAREN NAME RPAREN'
    p[0] = p[3]


def p_expression_init_valuation(p):
    'init_val : VALUATION LPAREN val RPAREN'
    p[0] = p[3]


def p_expression_valuationlist1(p):
    'val : valexpr'
    p[0] = [p[1]]


def p_expression_valuationlist(p):
    '''val : valexpr COMMA val COMMA
           | valexpr COMMA val'''
    p[0] = [p[1]] + p[3]


def p_expression_valuation2(p):
    'valexpr : NAME valexpr'
    p[0] = p[1] + p[2]


def p_expression_valuation(p):
    'valexpr : NAME'
    p[0] = p[1]
    # 'val : NAME EQUALS NAME'
    # p[0] = [p[1] + " " + p[2] + " " + p[3]]


def p_expression_flaggingstates(p):
    'flaggingstates : FLAGGING LPAREN statelist RPAREN'
    p[0] = p[3]


def p_expression_states(p):
    'states : STATES LPAREN statelist RPAREN'
    p[0] = p[3]


def p_expression_state_list(p):
    '''statelist :  NAME COMMA statelist COMMA
                  | NAME COMMA statelist'''
    p[0] = [p[1]] + p[3]


def p_expression_state_list2(p):
    'statelist : NAME'
    p[0] = [p[1]]


def p_expression_transitions(p):
    'transitions : TRANSITIONS LPAREN transitionlist RPAREN'
    p[0] = p[3]


def p_expression_transitionlist2(p):
    'transitionlist : transition'
    p[0] = [p[1]]


def p_expression_transitionlist(p):
    'transitionlist : transition COMMA transitionlist'
    p[0] = [p[1]] + p[3]


def p_expression_transition1(p):
    'transition : NAME ARROW NAME LPAREN condition RPAREN'
    condition = string_to_fol(" ".join(p[5]))
    action = []
    p[0] = [p[1], condition, action, p[3]]


def p_expression_transition2(p):
    'transition : NAME ARROW NAME LPAREN action RPAREN'
    condition = Atom("True")
    action = string_to_assignments(" ".join(p[5]))
    p[0] = [p[1], condition, action, p[3]]


def p_expression_transition3(p):
    'transition : NAME ARROW NAME LPAREN CONDACTDELIM action RPAREN'
    condition = Atom("True")
    action = string_to_assignments(" ".join(p[6]))
    p[0] = [p[1], condition, action, p[3]]


def p_expression_transition4(p):
    'transition : NAME ARROW NAME'
    condition = Atom("True")
    action = []
    p[0] = [p[1], condition, action, p[3]]


def p_expression_transition(p):
    'transition : NAME ARROW NAME LPAREN condition CONDACTDELIM action RPAREN'
    condition = string_to_fol(" ".join(p[5]))
    action = string_to_assignments(" ".join(p[7]))
    p[0] = [p[1], condition, action, p[3]]


def p_expression_condition(p):
    'condition : NAME'
    p[0] = [p[1]]


def p_expression_condition2(p):
    'condition : condition NAME'
    p[0] = p[1] + [p[2]]


def p_expression_action(p):
    'action : NAME'
    p[0] = [p[1]]


def p_expression_action2(p):
    'action : action NAME'
    p[0] = p[1] + [p[2]]


class error:
    text: str


# Error rule for syntax errors
def p_error(p):
    print("Syntax error caused by token " + str(p) + " when trying to parse monitor: " + error.text.replace("\n", ""))
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


def string_to_date(text: str) -> Monitor:
    error.text = text
    dt = parser.parse(text.replace("\n", " "), lexer=lexer)
    dt.reduce()
    return dt


if __name__ == "__main__":
    interactive_parser()
