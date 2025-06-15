import sexpdata
from dataclasses import dataclass
from enum import Enum
from typing import List,Tuple,Dict

class VarType(Enum):
    NAME = 0
    TEXT = 1
    SKEY = 2
    AKEY = 3
@dataclass
class Variable:
    var_name: str
    var_type: VarType
    def __str__(self) -> str:
        return self.var_name
    def __repr__(self) -> str:
        return f"{self.var_type}:{self.var_type}"

VarMap = Dict[str,Variable]

@dataclass
class LtkTerm:
    agent1_name: str
    agent2_name: str
    def __repr__(self):
        return f"(ltk {self.agent1_name} {self.agent2_name})"
    def __str__(self):
        return self.__repr__()
@dataclass
class PubkTerm:
    agent_name:str
    def __repr__(self):
        return f"(pubk {self.agent_name})"
    def __str__(self):
        return self.__repr__()
@dataclass
class PrivkTerm:
    agent_name:str
    def __repr__(self):
        return f"(privk {self.agent_name})"
KeyTerm = LtkTerm | PubkTerm | PrivkTerm | Variable

@dataclass
class EncTerm:
    data: List["NonCatTerm"]
    key: KeyTerm
    def __repr__(self):
        data_str = ' '.join([f"{msg}" for msg in self.data])
        return f"(enc {data_str} {self.key})"
@dataclass
class CatTerm:
    data: List["NonCatTerm"]
    def __repr__(self):
        data_str = ' '.join([f"{msg}" for msg in self.data])
        return f"(cat {data_str})"
class SendRecv(Enum):
    SEND = 0
    RECV = 1
Message = Variable | EncTerm | CatTerm | KeyTerm
NonCatTerm = KeyTerm | EncTerm
IndvTrace = Tuple[SendRecv,Message]
MessageTrace = List[IndvTrace]

def trace_to_str(send_recv_msg:Tuple[SendRecv,Message]):
    send_recv,message = send_recv_msg
    match send_recv:
        case SendRecv.SEND:
            return f"(send {message})"
        case SendRecv.RECV:
            return f"(send {message})"
def var_declarations_to_str(var_map_str:VarMap):
    type_to_var_name:Dict[VarType,List[str]] = {}
    for var_name,variable in var_map_str.items():
        var_type = variable.var_type
        if var_type not in type_to_var_name:
            type_to_var_name[var_type] = []
        type_to_var_name[var_type].append(var_name)

    one_type_var_declarations_arr = []
    for var_type,var_names in type_to_var_name.items():
        all_var_names = ' '.join(var_names)
        one_type_var_declarations_arr.append(f"({all_var_names} {var_type})")
    return ' '.join(one_type_var_declarations_arr)
@dataclass
class Role:
    role_name: str
    var_map: VarMap
    trace:MessageTrace
    def __repr__(self):
        var_map_str = var_declarations_to_str(self.var_map)
        trace_str = '\n'.join([trace_to_str(send_recv_msg) for send_recv_msg in self.trace])
        return (f"(defrole {self.role_name}"
                f"(vars {var_map_str})"
                f"(trace"
                f"{trace_str})"
                f")")
    def __str__(self):
        return self.__repr__()
@dataclass
class Protocol:
    protocol_name: str
    role_arr: List[Role]
    def __repr__(self):
        return (f"(defprotocol {self.protocol_name}"
                f"{' '.join([f"{role}" for role in self.role_arr])})")
    def __str__(self):
        return self.__repr__()
@dataclass
class Strand:
    role_name: str
    trace_len: int
    var_map: VarMap
    def __repr__(self):
        var_to_var_map_str = ' '.join([ f"({var_name} {variable.var_name})" for var_name,variable in self.var_map.items()])
        return f"(defstrand {self.role_name} {self.trace_len} {var_to_var_map_str})"
    def __str__(self):
        return self.__repr__()
BaseTerm = Variable | KeyTerm
@dataclass
class NonOrig:
    terms: List[BaseTerm]
    def __repr__(self):
        return f"(non-orig {' '.join(f"{term}" for term in self.terms)})"
    def __str__(self):
        return self.__repr__()
@dataclass
class UniqOrig:
    terms: List[BaseTerm]
    def __repr__(self):
        return f"(uniq-orig {' '.join(f"{term}" for term in self.terms)})"
    def __str__(self):
        return self.__repr__()
Constraint = Strand | NonOrig | UniqOrig

@dataclass
class Skeleton:
    protocol_name: str
    vars_list: VarMap
    constraints_list: List[Constraint]
    def __repr__(self):
        constraints_str = '\n'.join([f"{constraint}" for constraint in self.constraints_list])
        return (f"(defskeleton {self.protocol_name}"
                f"(vars {var_declarations_to_str(self.vars_list)})"
                f"{constraints_str})")
"""list of strings appearing in CPSA syntax collected here so prevent
repetion and avoid inconsistencies"""

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
PRIVK_STR = "privk"
NAME_STR = "name"
TEXT_STR = "text"
SKEY_STR = "skey"
AKEY_STR = "akey"

KEY_CATEGORIES = [PRIVK_STR,PUBK_STR,LTK_STR]
MESSAGE_CATEGORIES = [ENC_STR,CAT_STR,LTK_STR,PUBK_STR,PRIVK_STR]

Sexp = sexpdata.Symbol | int | List[sexpdata.Symbol]

class ParseException(Exception):
    """parse exception used to signal an exception occured somewhere while transcribing"""
    pass

def s_expr_instead_of_str(expected_str:str,s_expr) -> ParseException:
    """function to generate a common exception where there should have been a simple string but found an s-expression instead"""
    return ParseException(f"Expected '{expected_str}' string not an s expression {str(s_expr)} with type {type(s_expr)}")

def unexpected_str_error(expected_str:str,unexpected_str:str) -> ParseException:
    """function to generate a common exception where the s_expr contains an unexpected string
    Ex: expected defprotocol at beginning of protocol but saw something else"""
    return ParseException(f"Expected '{expected_str}' string at beginning of s expression not {unexpected_str}")

def is_symbol_type(symbl) -> bool:
    return type(symbl) == sexpdata.Symbol or type(symbl) == str

def match_type_and_str(s_expr,expected_str:str) -> None:
    """helper function to check that an s-expr is a specific string like defprotocol"""
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(expected_str,s_expr)
    if str(s_expr) != expected_str:
        raise unexpected_str_error(expected_str,str(s_expr))
def get_var(var_name:str,var_dict:VarMap) -> Variable:
    if var_name not in var_dict:
        raise ParseException(f"{var_name} is not in {var_dict}")
    return var_dict[var_name]
def get_str_from_symbol(s_expr:sexpdata.Symbol,data_name:str) -> str:
    """simply gets the string from an s-expr"""
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(data_name,s_expr)
    return str(s_expr)
def match_var_and_type(var_name:str,var_dict:VarMap,var_type:VarType) -> None:
    if var_name not in var_dict:
        raise ParseException(f"{var_name} is not in {var_dict}")
    variable = var_dict[var_name]
    if variable.var_type != var_type:
        raise ParseException(f"{var_name} has type {variable.var_type} doesn't match {var_type}")
def str_to_vartype(var_type_str:str):
    """convert string of vartype to VarType Enum object,
    used for parsing var name in variable declarations"""
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
    """convert vartype to string used when transcribing"""
    var_type_to_str = {
        VarType.NAME : NAME_STR,
        VarType.TEXT : TEXT_STR,
        VarType.SKEY : SKEY_STR,
        VarType.AKEY : AKEY_STR
    }
    return var_type_to_str[var_type]


