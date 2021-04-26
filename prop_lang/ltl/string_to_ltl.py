import ply.yacc as yacc
from pip._vendor.distlib.compat import raw_input
from ply import lex

from prop_lang import formula
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp

tokens = (
    'G',
    'F',
    'U',
    'X',
    'And',
    'Or',
    'Not',
    'Implies',
    'IFF',
    'Open',
    'Close',
    'Atom'
)

t_G = r"G"
t_F = r"F"
t_U = r"U"
t_X = r"X"
t_Not = r"!"
t_And = r"&+"
t_Or = r"\|+"
t_Implies = r"(-|=)+>"
t_IFF = r"<(-|=)+>"
t_Open = r"\("
t_Close = r"\)"


# # A regular expression rule with some action code
def t_Atom(t):
    r"[a-zA-EH-TV-WY-Z0-9_\-][a-zA-Z0-9_\-]*|([a-zA-Z0-9_\-][a-zA-Z0-9_\-]+)"
    # keywords (G, F, U) not allowed in single letter atoms
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


def p_expression(p):
    '''expression : uni_expression
                | bi_expression
                | atom_expression
                | bracketed_expression'''
    p[0] = p[1]


def p_bracketed_expression(p):
    '''bracketed_expression : Open expression Close'''
    p[0] = p[2]


def p_expression_uni(p):
    '''uni_expression : G expression
                       | F expression
                       | X expression
                       | Not expression'''
    p[0] = UniOp(str(p[1]), p[2])


def p_expression_bi(p):
    '''bi_expression : expression U expression
                     | expression Or expression
                     | expression And expression
                     | expression Implies expression
                     | expression IFF expression'''
    p[0] = BiOp(p[1], str(p[2]), p[3])


def p_expression_atom(p):
    '''atom_expression : Atom'''
    p[0] = Atom(p[1])


class error:
    text: str


# Error rule for syntax errors
def p_error(p):
    print("Syntax error caused by token " + str(p) + " when trying to parse LTL: " + error.text.replace("\n", ""))
    raise SyntaxError


# Build the parser
parser = yacc.yacc(errorlog=yacc.NullLogger())


def interactive_parser():
    while True:
        try:
            s = raw_input('calc > ')
        except EOFError:
            break
        if not s: continue
        result = parser.parse(s)
        print(result)


def string_to_ltl(text: str) -> formula:
    error.text = text
    return parser.parse(text, lexer=lexer)
