import sexpdata
from typing import *
from enum import Enum

def load_cspa_as_s_expr(file):
    for line in file:
        break
    file_txt = file.read()
    result = sexpdata.loads(file_txt)
    return result

class VarType(Enum):
    NAME = 1
    TEXT = 2
    SKEY = 3
    AKEY = 4

NAME_STR = "name"
TEXT_STR = "text"
SKEY_STR = "skey"
AKEY_STR = "akey"

def str_to_vartype(var_type_str:str):
    var_type_str_to_type_dict = {
        NAME_STR : VarType.NAME,
        TEXT_STR : VarType.TEXT,
        SKEY_STR : VarType.SKEY,
        AKEY_STR : VarType.AKEY
    }
    if var_type_str in var_type_str_to_type_dict:
        return var_type_str_to_type_dict[var_type_str]
    raise ParseException(f"Error unknown message type {var_type_str} seen")
def vartype_to_str(var_type:VarType):
    var_str_to_var_type_dict = {
        VarType.NAME : NAME_STR,
        VarType.TEXT : TEXT_STR,
        VarType.SKEY : SKEY_STR,
        VarType.AKEY : AKEY_STR
    }
    if var_type in var_str_to_var_type_dict:
        return var_str_to_var_type_dict[var_type]
    raise ParseException(f"Unknown var_type {var_type}")
class Variable:
    def __init__(self,var_name:str,var_type:VarType):
        self.var_name = var_name
        self.var_type = var_type
    def __str__(self):
        return f"Variable({self.var_name},{self.var_type})"
    __repr__ = __str__
class MsgType(Enum):
    ENCRYPTED_TERM = 1
    CAT_TERM = 2
    ATOM_TERM = 3
    LTK_TERM = 4
    PUBK_TERM = 5
    ##have to add privk forgot to deal with that
class Message:
    def __init__(self,msg_type:MsgType,args_arr:Union[List['Message'],Variable]):
        self.msg_type = msg_type
        self.msg_data = args_arr
    def __str__(self):
        return f"Message({self.msg_type},{self.msg_data})"
    def __repr__(self):
        return self.__str__()
class SendRecv(Enum):
    SEND_TRACE = 1
    RECV_TRACE = 2
class Role:
    def __init__(self,role_name:str,var_dict:Dict[str,Variable],msg_trace:List[Tuple[SendRecv,Message]]):
        self.role_name = role_name
        self.var_dict = var_dict
        self.msg_trace = msg_trace
    def __str__(self):
        return f"Role({self.role_name},{self.var_dict},{self.msg_trace})"
    def __repr__(self):
        return self.__str__()
class Protocol:
    def __init__(self,roles_arr:List[Role],prot_name:str,basic_str:str):
        self.roles_arr = roles_arr
        self.prot_name = prot_name
        self.basic_str = basic_str
    def __str__(self):
        return f"Protocol(\n{self.roles_arr},\n{self.prot_name},\n{self.basic_str})"
    def __repr__(self):
        return self.__str__()
class Strand:
    #i think trace len is being ignored for now?
    def __init__(self,role_name:str,trace_len:int,var_map:Dict[str,Variable]):
        self.role_name = role_name
        self.trace_len = trace_len
        self.var_map = var_map
class ConstrType(Enum):
    UNIQ_ORIG = 0
    NON_ORIG = 1
class Constraint:
    def __init__(self,constr_type:ConstrType,msg_on_constr:Message):
        self.constr_type = constr_type
        self.msg_on_constr = msg_on_constr
class Skeleton:
    def __init__(self,skelet_name:str,var_dict:Dict[str,Variable],strand_list:List[Strand],orig_constr:List[Constraint]):
        self.skelet_name = skelet_name
        self.var_dict = var_dict
        self.strand_list = strand_list
        self.orig_constr = orig_constr

class ParseException(Exception):
    def __init__(self,message):
        self.message = message
        super().__init__(message)

DEF_PROT_STR = "defprotocol"
DEF_SKEL_STR = "defskeleton"
DEF_STRAND_STR = "defstrand"
NON_ORIG_STR = "non-orig"
UNIQ_ORIG_STR = "uniq-orig"
BASIC_STR = "basic"
DEF_ROLE_STR = "defrole"
VARS_STR = "vars"  
TRACE_STR = "trace"
SEND_STR = "send"
RECV_STR = "recv"
ENC_STR = "enc"
CAT_STR = "cat"
LTK_STR = "ltk"
PUBK_STR = "pubk"

def s_expr_instead_of_str(expected_str:str,s_expr) -> ParseException:
    return ParseException(f"Expected '{expected_str}' string not an s expression {str(s_expr)} with type {type(s_expr)}")

def unexpected_str_error(expected_str:str,unexpected_str:str) -> ParseException:
    return ParseException(f"Expected '{expected_str}' string at beginning of s expression not {unexpected_str}")


def get_var(var_name_str:str,variable_dict:Dict[str,Variable]) -> Variable:
    if var_name_str not in variable_dict:
        raise ParseException(f"Unknown Variable Name {var_name_str} known variables are {variable_dict.keys()}")
    return variable_dict[var_name_str]

def is_symbol_type(symbl) -> bool:
    return type(symbl) == sexpdata.Symbol

def match_type_and_str(s_expr,expected_str:str) -> None:
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(expected_str,s_expr)
    if str(s_expr) != expected_str:
        raise unexpected_str_error(expected_str,str(s_expr))


def match_var_type(var:Variable,expected_var_type:VarType) -> None:
    if var.var_type != expected_var_type:
        raise ParseException(f"Expected var type = {vartype_to_str(expected_var_type)} but got {vartype_to_str(var.var_type)}")

def get_str_from_symbol(s_expr:sexpdata.Symbol,data_name:str) -> str:
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(data_name,s_expr)
    return str(s_expr)

def parse_vars_list(s_expr,var_dict) -> None:
    if len(s_expr) < 2:
        raise ParseException(f"Expected variable name and type not {str(s_expr)}")
    data_type_str = get_str_from_symbol(s_expr[-1],"variable type")
    data_type = str_to_vartype(data_type_str)
    for elm in s_expr[:-1]:
        cur_var_str = get_str_from_symbol(elm,"variable name")
        cur_var = Variable(cur_var_str,data_type)
        if cur_var in var_dict:
            raise ParseException(f"Repeated variable name {cur_var_str}")
        var_dict[cur_var_str] = cur_var 
    
def parse_vars_clause(s_expr) -> Dict[str,Variable]:
    var_dict = {}
    if len(s_expr) < 2:
        raise ParseException(f"Expected 'vars' and variables list in the s expression but length of s expression is = {len(s_expr)}")
    for elm in s_expr[1:]:
        parse_vars_list(elm,var_dict)
    return var_dict

#parses encrypted term and cat term for now
def parse_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    if type(s_expr) == sexpdata.Symbol:
        var_name = get_str_from_symbol(s_expr,"var name")
        var = get_var(var_name,var_dict)
        return Message(MsgType.ATOM_TERM,var)
    if len(s_expr) < 1:
        raise ParseException(f"empty s-expr cannot be a term")
    
def parse_ltk(s_expr,var_dict:Dict[str,Variable]) -> Message:
    if len(s_expr) != 3:
        raise ParseException(f"Expected s-expr of length 3 ltk name1 name2 but length is {len(s_expr)}")
    str_name_1 = get_str_from_symbol(s_expr[1],"name1 in ltk")
    str_name_2 = get_str_from_symbol(s_expr[2],"name2 in ltk")
    name_1 = get_var(str_name_1,var_dict)
    name_2 = get_var(str_name_2,var_dict)
    if name_1.var_type != VarType.NAME:
        raise ParseException(f"Expected variable type {vartype_to_str(VarType.NAME)} got {vartype_to_str(name_1.var_type)}")
    if name_2.var_type != VarType.NAME:
        raise ParseException(f"Expected variable type {vartype_to_str(VarType.NAME)} got {vartype_to_str(name_2.var_type)}")
    name_1_term = Message(MsgType.ATOM_TERM,name_1)
    name_2_term = Message(MsgType.ATOM_TERM,name_2)
    return Message(MsgType.LTK_TERM,[name_1_term,name_2_term])

def parse_pubk(s_expr,var_dict:Dict[str,Variable]) -> Message:
    if len(s_expr) != 2:
        raise ParseException(f"Expected s-expr of length 2 pibk name but length is {len(s_expr)} s_expr is {str(s_expr)}")
    str_name = get_str_from_symbol(s_expr[1],"name in pubk")
    name = get_var(str_name,var_dict)
    if name.var_type != VarType.NAME:
        raise ParseException(f"Expected variable type {vartype_to_str(VarType.NAME)} got {vartype_to_str(name.var_type)}")
    name_term = Message(MsgType.ATOM_TERM,name)
    return Message(MsgType.PUBK_TERM,[name_term])

def is_valid_key(msg:Message) -> bool:
    if msg.msg_type in [MsgType.PUBK_TERM,MsgType.LTK_TERM]:
        return True
    if msg.msg_type == MsgType.ATOM_TERM and msg.msg_data.var_type in [VarType.AKEY,VarType.SKEY]:
        return True
    return False
def parse_enc_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    if len(s_expr) < 3:
        raise ParseException(f"Expected atleast three terms enc,message and encryption key")
    data_terms_lst = [parse_term(t,var_dict) for t in s_expr[1:-1]]
    key_term_expr = s_expr[-1]
    key_term = parse_term(key_term_expr,var_dict)
    if not is_valid_key(key_term):
        raise ParseException(f"Expected term of type key but got {str(s_expr)}")
    data_terms_lst.append(key_term)
    return Message(MsgType.ENCRYPTED_TERM,data_terms_lst)

##condenses any nested cat term not used any example yet will impl later
def condense_cat_term(msg_list:List[Message]) -> Message:
    pass
def parse_cat_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    if len(s_expr) < 1:
        raise ParseException(f"Expected atleast two terms cat and some data")
    data_terms_lst = [parse_term(t,var_dict) for t in s_expr[1:]]
    return Message(MsgType.CAT_TERM,data_terms_lst)


def parse_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    if type(s_expr) == sexpdata.Symbol:
        #is simple string variable
        var_term_name = get_str_from_symbol(s_expr,"message term")
        var_term = get_var(var_term_name,var_dict)
        return Message(MsgType.ATOM_TERM,var_term)
    if len(s_expr) < 2:
        raise ParseException(f"Since s-expr in message expected enc or cat followed by message term")
    enc_cat_ltk_pubk_str = get_str_from_symbol(s_expr[0],"enc/cat/ltk/pubk")        
    func_dict = {
        ENC_STR  : parse_enc_term,
        CAT_STR  : parse_cat_term,
        LTK_STR  : parse_ltk,
        PUBK_STR : parse_pubk
    }
    if enc_cat_ltk_pubk_str not in func_dict:
        raise ParseException(f"Expected s-expr message term to start with enc/cat/pubk/ltk not {enc_cat_ltk_pubk_str}")    
    return func_dict[enc_cat_ltk_pubk_str](s_expr,var_dict)

def parse_indv_trace(s_expr,var_dict) -> Tuple[SendRecv,Message]:
    if len(s_expr) != 2:
        raise ParseException(f"Expected send/recv followed by message as s_expr len(s_expr) is: {len(s_expr)}")
    send_or_recv_str = get_str_from_symbol(s_expr[0],"send/recv")    
    if send_or_recv_str != SEND_STR and send_or_recv_str != RECV_STR:
        raise ParseException(f"Expected send/recv clause not {send_or_recv_str}")
    ##currently expecting only one s_expr later if sending multiple 
    ##messages deal with having cat instead
    trace_type = SendRecv.SEND_TRACE if send_or_recv_str == SEND_STR else SendRecv.RECV_TRACE
    return trace_type,parse_term(s_expr[1],var_dict)

def parse_trace(s_expr,var_dict) -> List[Tuple[SendRecv,Message]]:
    #currently forcing limit of 3 becuase the current racket code seems 
    #to have that restriction as well will see what to do with this later
    if len(s_expr) < 3:
        raise ParseException(f"Expecred 'trace' and atleast two messages current length of s_expr is: {len(s_expr)}")        
    match_type_and_str(s_expr[0],TRACE_STR)
    result = []
    for indv_trace in s_expr[1:]:
        result += [parse_indv_trace(indv_trace,var_dict)]
    return result

def parse_role(s_expr) -> Role:
    if len(s_expr) != 4:
        raise ParseException(f"Expected 'defrole',role_name,variables list and trace of sends and receives but length of s expr is {len(s_expr)}")
    match_type_and_str(s_expr[0],DEF_ROLE_STR)
    role_name = get_str_from_symbol(s_expr[1],"role name")
    var_dict = parse_vars_clause(s_expr[2])
    msg_trace = parse_trace(s_expr[3],var_dict)

    return Role(role_name,var_dict,msg_trace)    

def parse_protocol(s_expr) -> Protocol:
    if len(s_expr) < 4:
        raise ParseException(f"Expected 'defprotocol',protocol name,'basic' and atleast one role but size of s_expr is = {len(s_expr)}")
    match_type_and_str(s_expr[0],DEF_PROT_STR)

    prot_name = get_str_from_symbol(s_expr[1],"protocol name")
    match_type_and_str(s_expr[2],BASIC_STR)
    
    return Protocol([parse_role(role_expr) for role_expr in s_expr[3:]],prot_name,BASIC_STR)    

def parse_strand(s_expr):
    pass
def parse_non_orig(s_expr):
    pass 
def parse_uniq_orig(s_expr):
    pass
def parse_skeleton(s_expr):
    if len(s_expr) == 0:
        raise ParseException("Empty S expression expected defskeleton as first element")
    match_type_and_str(s_expr[0],DEF_SKEL_STR)
    skelet_name = get_str_from_symbol(s_expr[1],"skeleton name")
    var_dict = parse_vars_clause

    strands_list = []
    constr_arr = []

    for sub_s_expr in s_expr[3:]:
        first_str = get_str_from_symbol(sub_s_expr[1],"defstrand/non-orig/uniq-orig")
        if first_str == DEF_STRAND_STR:
            strands_list.append(parse_strand(sub_s_expr))
        elif first_str == NON_ORIG_STR:
            constr_arr.append(parse_non_orig(sub_s_expr))
        elif first_str == UNIQ_ORIG_STR:
            constr_arr.append(parse_uniq_orig(sub_s_expr))

def parse_file(s_expr):
    if len(s_expr) == 0:
        raise ParseException("Empty S expression expected defprotocol clause")
    if len(s_expr) == 1:
        return parse_protocol(s_expr[0])
    if len(s_expr) == 2:
        return [parse_protocol(s_expr[0]),parse_skeleton(s_expr[1])]
    if len(s_expr) > 2:
        raise ParseException("Expected only two s-expr for protocol and skeleton respectively")
    