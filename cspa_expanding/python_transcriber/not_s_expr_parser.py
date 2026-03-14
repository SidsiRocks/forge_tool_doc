import ply.yacc as yacc
import sys
from collections import defaultdict

from not_s_expr_lexer import tokens
from type_and_helpers import *

# TODO: see if it is possible to add type hints to these parsing functions as well
@dataclass
class Statement:
    sender: str
    reciever: str
    gen_list: List[str]
    message: Message
    def __str__(self) -> str:
        gen_list_str = "" if len(self.gen_list) == 0 else f"{self.gen_list} "
        return f"{self.sender}->{self.reciever}: {gen_list_str}{self.message}"
    def __repr__(self) -> str:
        return self.__str__()

start = 'protocol'

def p_send_recv(p):
    '''send_recv : VAR_NAME ARROW VAR_NAME COLON'''
    p[0] = (p[1],p[3])

def p_statement(p):
    '''statement : send_recv '[' var_list ']' message
                 | send_recv message'''
    if len(p) == 6:
        sender,reciever = p[1]
        gen_list,message = p[3],p[5]
        p[0] = Statement(sender,reciever,gen_list,message)
    else:
        sender,reciever = p[1]
        gen_list,message = [],p[2]
        p[0] = Statement(sender,reciever,gen_list,message)

def p_stmnt_lst(p):
    '''stmnt_lst : statement
                 | stmnt_lst statement'''
    if len(p) == 3:
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]
def p_protocol(p):
    '''protocol : VAR_NAME COLON stmnt_lst'''
    p[0] = p[1],p[3]

def p_var_list(p):
    '''var_list : var_list ',' VAR_NAME
                | VAR_NAME'''
    if len(p) == 3:
        p[1].append(p[3])
        p[0] = p[1]
    else:
        p[0] = [p[1]]

def p_message(p):
    '''message : nonce
              | name
              | tuple
              | func_apply'''
    p[0] = p[1]

def p_msg_list(p):
    '''msg_list : msg_list ',' message
               | message'''
    if len(p) == 4:
        p[1].append(p[3])
        p[0] = p[1]
        # print("message list with: ",p[0])
    else:
        p[0] = [p[1]]
        # print("base message list with: ",p[0])

def p_nonce(p):
    '''nonce : NONCE_PRE VAR_NAME'''
    p[0] = Variable(p[2],MsgTypes.TEXT)
def p_name(p):
    '''name : NAME_PRE VAR_NAME'''
    p[0] = Variable(p[2],MsgTypes.NAME)

def p_tuple(p):
    '''tuple : '<' msg_list '>' '''
    p[0] = CatTerm(p[2])
def p_func_apply(p) -> Message:
    '''func_apply : VAR_NAME '(' msg_list ')' '''
    def message_is_akey(msg:Message) -> KeyTerm|None:
        match msg:
            case PubkTerm(_) | PrivkTerm(_):
                return msg
            case Variable(var_name,var_type):
                if var_type in [MsgTypes.AKEY]:
                    return msg
        return None
    def message_is_skey(msg:Message) -> KeyTerm|None:
        match msg:
            case LtkTerm(_):
                return msg
            case Variable(var_name,var_type):
                if var_type in [MsgTypes.SKEY]:
                    return msg
        return None
    def message_is_name_raise(msg:Message) -> str:
        match msg:
            case Variable(var_name,var_type):
                if var_type != MsgTypes.NAME:
                    raise ParseException("Expected variable of type name as argument")
                return var_name
            case _:
                raise ParseException("Expected simple variable here not complex message type")
    def a_enc(arg_list:List[Message]):
        if len(arg_list) != 2:
            raise ParseException(f"Expected 2 arguments to a_enc, plaintext,key got {len(arg_list)} arg_list:{arg_list}")
        plain_text = arg_list[0]
        match plain_text:
            case CatTerm(_):
                pass
            case _:
                plain_text = CatTerm([plain_text])

        key = arg_list[1]
        match message_is_akey(key):
            case None:
                raise ParseException(f"Expected akey as as second argument to aenc")
            case key:
                return EncTerm(plain_text.data,key)
    def s_enc(arg_list:List[Message]):
        if len(arg_list) != 2:
            raise ParseException(f"Expected 2 arguments to s_enc, plaintext,key got {len(arg_list)}")
        plain_text = arg_list[0]
        match plain_text:
            case CatTerm(_):
                pass
            case _:
                plain_text = CatTerm([plain_text])

        key = arg_list[1]
        match message_is_skey(key):
            case None:
                raise ParseException(f"Expected skey as as second argument to senc")
            case key:
                return EncTerm(plain_text.data,key)
    def pubk(arg_list:List[Message]):
        if len(arg_list) != 1:
            raise ParseException(f"Expected 1 argument to function name got {len(arg_list)}")
        name = message_is_name_raise(arg_list[0])
        return PubkTerm(name)
    def privk(arg_list:List[Message]):
        if len(arg_list) != 1:
            raise ParseException(f"Expected 1 argument to function name got {len(arg_list)}")
        name = message_is_name_raise(arg_list[0])
        return PrivkTerm(name)
    def ltk(arg_list:List[Message]):
        if len(arg_list) != 2:
            raise ParseException(f"Expected 2 argument to ltk got {len(arg_list)}")
        name0,name1 = message_is_name_raise(arg_list[0]),message_is_name_raise(arg_list[1])
        return LtkTerm(name0,name1)
    def hash_term(arg_list:List[Message]):
        if len(arg_list) != 1:
            raise ParseException(f"Expected 1 argument to hash got {len(arg_list)}")
        # TODO: CatTerm should also work here now that we have introduced tuple, will fix
        return HashTerm(arg_list[0])

    func_name,arg_list = p[1],p[3]
    func_name_to_func = {
        "aenc" : a_enc,
        "senc" : s_enc,
        "pubk" : pubk,
        "privk": privk,
        "ltk": ltk,
        "hash": hash_term
    }
    if func_name not in func_name_to_func:
        raise ParseException(f"{func_name} not in list of supported function names {func_name_to_func.keys()}")
    else:
        p[0] = func_name_to_func[func_name](arg_list)

def p_error(p):
    if p:
         print("Syntax error at token", p.type)
         raise ParseException(p)
         # Just discard the token and tell the parser it's okay.
         parser.errok()
    else:
         print("Syntax error at EOF")


parser = yacc.yacc()

def convert_parse_tree(prot_name:str,statements:List[Statement]):
    def validate_trace(trace:List[Tuple[SendRecv,Message]]):
        length = len(trace)
        for i in range(1,length):
            cur_send_recv,_ = trace[i]
            prev_send_recv,_ = trace[i-1]
            if cur_send_recv == prev_send_recv:
                raise ParseException(f"In trace\n{trace}\nconsecutive sends and recieves")

    role_name_to_trace: Dict[str,List[Tuple[SendRecv,Message]]] = defaultdict(list)

    for stmnt in statements:
        role_name_to_trace[stmnt.sender].append((SendRecv.SEND ,stmnt.message))
        role_name_to_trace[stmnt.reciever].append((SendRecv.RECV,stmnt.message))

    role_arr: List[Role] = []
    for role_name,trace in role_name_to_trace.items():
        validate_trace(trace)
        this_role_vars = set()
        for _,msg in trace:
            get_vars_in_msg(msg,this_role_vars)
        var_map = {var.var_name:var for var in this_role_vars}
        # can infer some role constraints from nonces in generated list
        role_arr.append(Role(role_name,var_map,trace,role_constraints=[]))

    return Protocol(prot_name,role_arr)


if __name__ == "__main__":
    file_name = sys.argv[1]
    with open(file_name) as file:
        prot_name,result = parser.parse(file.read())
        print("prot_name: ",prot_name)
        for elm in result:
            print(elm)
        prot = convert_parse_tree(prot_name,result)
        print("converted protocol is: ")
        print(prot)

