import ply.lex as lex
import sys

tokens = (
    "VAR_NAME",
    "NUM",
    "ARROW",
    # "L_SQR","R_SQR",
    # "L_PAREN","R_PAREN",
    # "L_ANGLE","R_ANGLE",
    "COLON",
    "NONCE_PRE","NAME_PRE",
    "BOUNDS_KEYWORD"
    # add prefix for skey and akey which can also be generated so wouldn't always come from functions
)

literals = ['[',']','(',')','<','>',',',':','{','}']
# literals = ['[',']','(',')','<','>',',',':']

t_VAR_NAME = r'[A-Za-z_][A-Za-z_0-9]*'
t_ARROW = r'\-\>'
t_NONCE_PRE,t_NAME_PRE = r'~',r"\$"
t_ignore = ' \t\n'
t_COLON = r':'

def t_BOUNDS_KEYWORD(t):
    r'Bounds'
    return t

def t_NUM(t):
    r'\d+'
    t.value = int(t.value)
    return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_comment(_):
    r'\#.*'
    pass

def t_error(t):
    raise RuntimeError(f"Unrecognized characters: {t.value[0]}\n{t.value}")

lexer = lex.lex()

if __name__ == '__main__':
    file_name = sys.argv[1]
    with open(file_name) as file:
        lexer.input(file.read())
        while True:
            tok = lexer.token()
            if not tok:
                break
            print(tok)
