from sexpdata import loads
from typing import *
from enum import Enum

def load_cspa_as_s_expr(file):
    for line in file:
        break
    file_txt = file.read()
    result = loads(file_txt)
    return result

class VarType(Enum):
    NAME = 1
    TEXT = 2
    SKEY = 3
    AKEY = 4
class Variable:
    def __init__(self,var_name:str,msg_type:VarType):
        self.var_name = var_name
        self.msg_type = msg_type
class MsgType(Enum):
    ENCRYPTED_TERM = 1
    VAR_ATOM = 2
    SET_MSGS = 3
class Message:
    def __init__(self,msg_type:MsgType,args_arr:List['Message']):
        self.msg_type = msg_type
        self.msg_data = args_arr
class Role:
    def __init__(self,role_name:str,vars_list:List[Variable],msg_trace:List[Message]):
        self.role_name = role_name
        self.vars_list = vars_list
        self.msg_trace = msg_trace
class Protocol:
    def __init__(self,roles_arr:List[Role],prot_name:str,basic_str:str):
        self.roles_arr = roles_arr
        self.prot_name = prot_name
        self.basic_str = basic_str
file = open("../additional_enc_test/addit_enc.rkt",'r')
s_expr = load_cspa_as_s_expr(file) 
print(s_expr)

class ParseException(Exception):
    def __init__(self,message):
        self.message = message
        super().__init__(message)

DEF_PROT_STR = "defprotocol"
DEF_ROLE_STR = "defrole"
VARS_STR = "vars"
NAME_STR = "name"
TEXT_STR = "text"
SKEY_STR = "skey"
AKEY_STR = "akey"  

def parse_protocol(s_expr):
    if len(s_expr) == 0:
        return ParseException("Empty S expression expected defprotocol clause")
    if str(s_expr[0]) != DEF_PROT_STR:
        pass