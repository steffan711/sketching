import dynasty.ply.lex as lex
import dynasty.ply.yacc as yacc

## Lexical analysis

tokens = (
    'NAME', 'NUMBER',
)

literals = ['=', '-', '{', '}', '[', ']', '(', ')', ':', ',', '/']

# Tokens

t_NAME = r'[a-zA-Z_][a-zA-Z0-9_]*'


def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t

t_ignore = " \t\n"


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

# Build the lexer
lex.lex()

## Syntactic analysis

def p_start(p):
    "start : '(' NAME ',' quan other_quan ':' dep other_dep ')'"
    p[0] = (p[2], [p[4]] + p[5], [p[7]] + p[8])

def p_frac(p):
    " frac : expr '/' expr"
    x = (p[1], p[3])
    p[0] = x

def p_interval(p):
    "interval : '[' expr ',' expr ']'"
    x = (p[2], p[4])
    p[0] = x

def p_expr_uminus(p):
    "expr : '-' expr"
    p[0] = -p[2]

def p_expr_number(p):
    "expr : NUMBER"
    p[0] = p[1]

def p_expr_name(p):
    "expr : NAME"
    p[0] = p[1]

def p_partitioning(p):
    '''partitioning : NUMBER
                    | '(' frac other_frac ')' '''
    if (len(p) == 2):
        p[0] = p[1]
    elif (len(p) == 5):
        p[0] = [p[2]] + p[3]

def p_domain(p):
    '''domain : interval
              | set_of_val'''
    p[0] = p[1]

def p_set_of_val(p):
    "set_of_val : '{' expr other_val '}'"
    p[0] = [p[2]] + p[3]

def p_quan(p):
    "quan : '{' NAME ',' interval ',' partitioning '}'"
    x = (p[2], p[4], p[6])
    p[0] = x

def p_dep(p):
    "dep : '{' NAME ',' domain '}'"
    p[0] = (p[2], p[4])


def p_empty(p):
    'empty :'
    pass

def data_formatter1(p):
    if (len(p) == 4):
        p[0] = [p[2]] + p[3]
    elif (len(p) == 2):
        p[0] = list()

def p_other_quan(p):
    '''other_quan : ',' quan other_quan
                  | empty'''
    data_formatter1(p)

def p_other_dep(p):
    '''other_dep : ',' dep other_dep
                  | empty'''
    data_formatter1(p)

def p_other_frac(p):
    '''other_frac : ',' frac other_frac
                  | empty'''
    data_formatter1(p)

def p_other_val(p):
    '''other_val : ',' expr other_val
                  | empty'''
    data_formatter1(p)


def p_error(p):
    if p:
        print("Syntax error at '%s'" % p.value)
    else:
        print("Syntax error at EOF")

#Build the parser
yacc.yacc()

def parse(data):
    parsed_data = yacc.parse(data)
    print(parsed_data)
    return parsed_data