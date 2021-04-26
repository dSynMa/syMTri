import ply.yacc as yacc

from pip._vendor.distlib.compat import raw_input
from ply import lex

from monitors.monitor import Monitor
from prop_lang import formula
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp

tokens = (
    'MathOp',
    'MathRel',
    'And',
    'Or',
    'Not',
    'Implies',
    'IFF',
    'Open',
    'Close',
    'Equal',
    'Var',
    'Val'
)

t_And = r"&+"
t_Or = r"\|+"
t_Not = r"!"
t_Implies = r"(\-|=)+>"
t_IFF = r"<(\-|=)+>"
t_Open = r"\("
t_Close = r"\)"
t_Equal = r"=+"


# # A regular expression rule with some action code
def t_Var(t):
    r"[a-zA-Z][a-zA-Z0-9_\-']*"
    return t

# # A regular expression rule with some action code
def t_MathOp(t):
    r"(\+|\-(?=[^(>|\-)])|%|/|\*)"
    return t

# # A regular expression rule with some action code
def t_MathRel(t):
    r"(<=(?=[^(=|\-|>)])|>=|<|>)"
    return t


def t_Val(t):
    r"[0-9]+"
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
                | bracketed_expression
                | var_expression
                | val_expression'''
    p[0] = p[1]


def p_bracketed_expression(p):
    '''bracketed_expression : Open expression Close'''
    p[0] = p[2]


def p_expression_uni(p):
    '''uni_expression : Not expression'''
    p[0] = UniOp(str(p[1]), p[2])


def p_expression_bi(p):
    '''bi_expression : expression Equal expression
                     | expression Or expression
                     | expression And expression
                     | expression Implies expression
                     | expression IFF expression
                     | math_expression MathRel math_expression'''
    p[0] = BiOp(p[1], str(p[2]), p[3])


def p_expression_math(p):
    '''math_expression : var_expression
                       | val_expression
                       | math_bi_expression'''
    p[0] = p[1]


def p_expression_math_bi(p):
    '''math_bi_expression : math_expression MathOp math_expression'''
    p[0] = BiOp(p[1], str(p[2]), p[3])



def p_expression_var(p):
    '''var_expression : Var'''
    p[0] = Atom(p[1])


def p_expression_val(p):
    '''val_expression : Val'''
    p[0] = Atom(p[1])


class error:
    text: str

# Error rule for syntax errors
def p_error(p):
    print("Syntax error caused by token " + str(p) + " when trying to parse first-order sentence: " + error.text.replace("\n", ""))
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
        result = parser.parse(s)
        print(result)


def string_to_fol(text: str) -> formula:
    error.text = text
    return parser.parse(text, lexer=lexer)
