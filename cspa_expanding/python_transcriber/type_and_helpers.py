import sexpdata
from dataclasses import dataclass
from enum import Enum
from typing import List,Tuple,Dict

class MsgTypes(Enum):
    NAME = 0
    TEXT = 1
    SKEY = 2
    AKEY = 3
    MESG = 4
    def __str__(self) -> str:
        vartype_to_str_dict = {
            MsgTypes.NAME : NAME_STR,
            MsgTypes.TEXT : TEXT_STR,
            MsgTypes.SKEY : SKEY_STR,
            MsgTypes.AKEY : AKEY_STR,
            MsgTypes.MESG : MESG_STR
        }
        return vartype_to_str_dict[self]

# VarTypeInConstraint needs to include strand types defined
# during runtime when roles are defined, but this type would
# only be allowed within the vars clause of a constraint hence
# this is needed
# TODO: can improve this VarType probably

@dataclass
class Variable:
    var_name: str
    var_type: MsgTypes
    def __str__(self) -> str:
        return self.var_name
    def __repr__(self) -> str:
        return f"{self.var_name}:{self.var_type}"

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
    def __str__(self) -> str:
        return self.__repr__()

@dataclass
class SeqTerm:
    #TODO: currently have seq inside seq might want to change that like we had for cat
    data: List["NonCatTerm"]
    def __repr__(self) -> str:
        data_str = ' '.join([f"{msg}" for msg in self.data])
        return f"(seq {data_str})"
    def __str__(self) -> str:
        return self.__repr__()

@dataclass
class HashTerm:
    hash_of: "NonCatTerm"
    def __repr__(self) -> str:
        return f"(hash {self.hash_of})"
    def __str__(self) -> str:
        return self.__repr__()

class SendRecv(Enum):
    SEND = 0
    RECV = 1
Message = Variable | EncTerm | CatTerm | KeyTerm | SeqTerm | HashTerm
NonCatTerm = KeyTerm | EncTerm | SeqTerm | HashTerm
IndvTrace = Tuple[SendRecv,Message]
MessageTrace = List[IndvTrace]

def trace_to_str(send_recv_msg:Tuple[SendRecv,Message]):
    send_recv,message = send_recv_msg
    match send_recv:
        case SendRecv.SEND:
            return f"(send {message})"
        case SendRecv.RECV:
            return f"(recv {message})"
def var_declarations_to_str(var_map_str:VarMap):
    type_to_var_name:Dict[MsgTypes,List[str]] = {}
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
    role_constraints:List["RoleConstraints"]
    def __repr__(self):
        var_map_str = var_declarations_to_str(self.var_map)
        trace_str = '\n'.join([trace_to_str(send_recv_msg) for send_recv_msg in self.trace])
        role_constrain_strs = '\n'.join(f"{constr}" for constr in self.role_constraints)
        result = None
        if len(self.role_constraints) == 0:
            result = (f"(defrole {self.role_name}"
                      f"(vars {var_map_str})"
                      f"(trace"
                      f"{trace_str})"
                      f")"
                      f")")
        else:
            result = (f"(defrole {self.role_name}"
                      f"(vars {var_map_str})"
                      f"(trace"
                      f"{trace_str})"
                      f")"
                      f"(constraint"
                      f"{role_constrain_strs}"
                      f")"
                      f")")
        return result
    def __str__(self):
        return self.__repr__()
@dataclass
class Protocol:
    protocol_name: str
    role_arr: List[Role]
    def __repr__(self):
        return (f"(defprotocol {self.protocol_name} basic"
                f"{' '.join([f"{role}" for role in self.role_arr])})")
    def __str__(self):
        return self.__repr__()
    def role_obj_of_name(self,role_name:str):
        for role in self.role_arr:
            if role.role_name == role_name:
                return role
        return None
@dataclass
class Strand:
    role_name: str
    trace_len: int
    skeleton_to_strand_var_map: VarMap
    def __repr__(self):
        var_to_var_map_str = ' '.join([ f"({var_name} {variable.var_name})" for var_name,variable in self.skeleton_to_strand_var_map.items()])
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
@dataclass
class FreshlyGenConstraint:
    terms: List[BaseTerm]
    def __repr__(self) -> str:
        terms_str = ' '.join(f"{term}" for term in self.terms)
        return f"(fresh-gen {terms_str})"
    def __str__(self):
        return self.__repr__()
@dataclass
class IndvSendRecvInConstraint:
    trace_type: SendRecv
    sender_reciever_strand: str
    message: Message
    def __repr__(self) -> str:
        match self.trace_type:
            case SendRecv.SEND:
                return f"({SEND_FROM_STR} {self.sender_reciever_strand} {self.message})"
            case SendRecv.RECV:
                return f"({RECV_BY_STR} {self.sender_reciever_strand} {self.message})"
    def __str__(self) -> str:
        return self.__repr__()
@dataclass
class TraceConstraint:
    trace_elms: List[IndvSendRecvInConstraint]
    trace_name: str
    def __repr__(self) -> str:
        trace_elms_str = '\n'.join([f"{trace_elm}" for trace_elm in self.trace_elms])
        return (f"(deftrace {self.trace_name}"
                f"{trace_elms_str}"
                f")")
    def __str__(self) -> str:
        return self.__repr__()
@dataclass
class NotEqConstraint:
    term1: BaseTerm
    term2: BaseTerm
    def __repr__(self) -> str:
        return f"(not-eq {self.term1} {self.term2})"
    def __str__(self) -> str:
        return self.__repr__()
Constraint = Strand | NonOrig | UniqOrig | TraceConstraint | NotEqConstraint
RoleConstraints = NonOrig | UniqOrig | NotEqConstraint | FreshlyGenConstraint

def strand_var_map_to_str(strand_vars_map:Dict[str,str]):
    strand_type_to_vars : Dict[str,List[str]] = {}
    for key,value in strand_vars_map.items():
        if value not in strand_type_to_vars:
            strand_type_to_vars[value] = []
        strand_type_to_vars[value].append(key)
    all_var_declarations : List[str] = []
    for strand_type,strand_vars in strand_type_to_vars.items():
        cur_str = f"({' '.join(strand_vars)} {strand_type})"
        all_var_declarations.append(cur_str)
    return " ".join(all_var_declarations)
@dataclass
class Skeleton:
    protocol_name: str
    non_strand_vars_map: VarMap
    strand_vars_map: Dict[str,str]
    constraints_list: List[Constraint]
    def __repr__(self):
        constraints_str = '\n'.join([f"{constraint}" for constraint in self.constraints_list])
        return (f"(defskeleton {self.protocol_name}"
                f"(vars {var_declarations_to_str(self.non_strand_vars_map)} {strand_var_map_to_str(self.strand_vars_map)})"
                f"{constraints_str})")
"""list of strings appearing in CPSA syntax collected here so prevent
repetion and avoid inconsistencies"""

# TODO can add a helper function which handles parsing enums encoded as strings
def get_role_sig_name(role:Role,protocol:Protocol):
    return f"{protocol.protocol_name}_{role.role_name}"
#TODO: can improve this should not need to do string mangling like this
def rolesig_of_role_obj_type(protocol:Protocol,role_obj_type:str):
    role_name = role_obj_type[5:]
    return f"{protocol.protocol_name}_{role_name}"

DEF_PROT_STR = "defprotocol"
DEF_SKEL_STR = "defskeleton"
DEF_STRAND_STR = "defstrand"
NON_ORIG_STR = "non-orig"
UNIQ_ORIG_STR = "uniq-orig"
NOT_EQ_STR = "not-eq"
DEF_TRACE_STR = "deftrace"
BASIC_STR = "basic"
DEF_ROLE_STR = "defrole"
VARS_STR = "vars"
TRACE_STR = "trace"
SEND_STR = "send"
RECV_STR = "recv"
SEND_FROM_STR = "send-from"
RECV_BY_STR = "recv-by"
ENC_STR = "enc"
CAT_STR = "cat"
SEQ_STR = "seq"
HASH_STR = "hash"
LTK_STR = "ltk"
PUBK_STR = "pubk"
PRIVK_STR = "privk"
MESG_STR = "mesg"
NAME_STR = "name"
TEXT_STR = "text"
SKEY_STR = "skey"
AKEY_STR = "akey"
ATTACKER_STR = "Attacker"
ROLE_CONSTR_STR = "constraint"
FRESH_GEN_STR = "fresh-gen"

KEY_CATEGORIES = [PRIVK_STR,PUBK_STR,LTK_STR]
MESSAGE_CATEGORIES = [ENC_STR,CAT_STR,LTK_STR,PUBK_STR,PRIVK_STR,SEQ_STR,HASH_STR]

Sexp = sexpdata.Symbol | int | List[sexpdata.Symbol]

predefined_constants : Dict[str,Variable] = {
    ATTACKER_STR : Variable(ATTACKER_STR,MsgTypes.NAME)
}

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
    return isinstance(symbl,sexpdata.Symbol) or isinstance(symbl,str)

def match_type_and_str(s_expr,expected_str:str) -> None:
    """helper function to check that an s-expr is a specific string like defprotocol"""
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(expected_str,s_expr)
    if str(s_expr) != expected_str:
        raise unexpected_str_error(expected_str,str(s_expr))
def get_var(var_name:str,var_dict:VarMap) -> Variable:
    #TODO: the function body counterintutive compared to definition see if can improve this
    if var_name not in var_dict and var_name not in predefined_constants:
        raise ParseException(f"{var_name} is not in {var_dict}")
    if var_name in var_dict:
        return var_dict[var_name]
    return predefined_constants[var_name]
def get_str_from_symbol(s_expr:sexpdata.Symbol,data_name:str) -> str:
    """simply gets the string from an s-expr"""
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(data_name,s_expr)
    return str(s_expr)
def get_int_from_symbol(s_expr,data_name:str) -> int:
    if not isinstance(s_expr,int):
        raise ParseException(f"Expected type int here not type {type(s_expr)} for {data_name}")
    return s_expr
def match_var_and_type(var_name:str,var_dict:VarMap,var_type:MsgTypes) -> None:
    if var_name not in var_dict:
        raise ParseException(f"{var_name} is not in {var_dict}")
    variable = var_dict[var_name]
    if variable.var_type != var_type:
        raise ParseException(f"{var_name} has type {variable.var_type} doesn't match {var_type}")

var_type_str_to_type_dict = {
    NAME_STR : MsgTypes.NAME,
    TEXT_STR : MsgTypes.TEXT,
    SKEY_STR : MsgTypes.SKEY,
    AKEY_STR : MsgTypes.AKEY,
    MESG_STR : MsgTypes.MESG
}

def str_to_vartype(var_type_str:str):
    """convert string of vartype to VarType Enum object,
    used for parsing var name in variable declarations"""
    if var_type_str in var_type_str_to_type_dict:
        return var_type_str_to_type_dict[var_type_str]
    raise ParseException(f"Error unknown message type {var_type_str} seen")
def vartype_to_str(var_type:MsgTypes):
    """convert vartype to string used when transcribing"""
    return f"{var_type}"

# added comment here to test commit all command
