import ply.yacc as yacc

from pip._vendor.distlib.compat import raw_input
from ply import lex

from monitors.monitor import Monitor
from prop_lang import formula
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp

tokens = (
    'SemiColon',
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
    'Assign',
    'Var',
    'Val'
)

t_SemiColon = r"(;|,)"
t_And = r"&+"
t_Or = r"\|+"
t_Not = r"!"
t_Implies = r"(\-|=)+>"
t_IFF = r"<(\-|=)+>"
t_Open = r"\("
t_Close = r"\)"
t_Equal = r"(?<!:)=+"
t_Assign = r":="


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


def p_expression1(p):
    '''expression : assignment_expression'''
    p[0] = [p[1]]


def p_expression_mult1(p):
    '''expression : assignment_expression SemiColon expression SemiColon'''
    p[0] = [p[1]] + p[3]


def p_expression_mult(p):
    '''expression : assignment_expression SemiColon expression'''
    p[0] = [p[1]] + p[3]


def p_assignment_expression(p):
    '''assignment_expression : var_expression Assign assigned_expression'''
    p[0] = BiOp(p[1], str(p[2]), p[3])


def p_assigned_expression(p):
    '''assigned_expression : uni_expression
                | bi_expression
                | bracketed_expression
                | var_expression
                | val_expression
                | math_bi_expression'''
    p[0] = p[1]


def p_bracketed_expression(p):
    '''bracketed_expression : Open assigned_expression Close'''
    p[0] = p[2]


def p_expression_uni(p):
    '''uni_expression : Not expression'''
    p[0] = UniOp(str(p[1]), p[2])


def p_expression_bi(p):
    '''bi_expression : assigned_expression Equal assigned_expression
                     | assigned_expression Or assigned_expression
                     | assigned_expression And assigned_expression
                     | assigned_expression Implies assigned_expression
                     | assigned_expression IFF assigned_expression
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
    print(
        "Syntax error caused by token " + str(p) + " when trying to parse assignments: " + error.text.replace("\n", ""))
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


def string_to_assignments(text: str) -> formula:
    error.text = text
    return parser.parse(text, lexer=lexer)
