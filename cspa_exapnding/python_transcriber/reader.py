import sexpdata
from typing import *
from enum import Enum
import io

def load_cspa_as_s_expr(file:io.TextIOWrapper):
    """reads the file and returns the s-expr of the 
    file (ignores first line which contains #lang/forge/domains/crypto)"""
    for line in file:
        break
    file_txt = file.read()
    result = sexpdata.loads(file_txt)
    return result
def get_root_s_expr_lst(txt:str):
    """the sexpdata library can only parse one s-expr by itself,multiple
    s-expr must be present as an array or similar,hence this adds a wrapper
    around that to find all s-expr"""
    brkt_count = 0
    brkt_started = False
    prev_indx = 0
    strs_so_far = []
    for indx,chr in enumerate(txt):
        if chr == '(':
            brkt_count += 1
            brkt_started = True
        elif chr == ')':
            brkt_count = brkt_count - 1
        if brkt_count == 0 and brkt_started:
            cur_s_expr_str = txt[prev_indx:(indx+1)]
            prev_indx = indx + 1
            brkt_started = False
            strs_so_far.append(cur_s_expr_str)
    return strs_so_far
def load_cspa_as_s_expr_new(file):
    """using get_root_s_expr_lst to parse multiple s-expr in one file"""
    result = []
    for line in file:
        break
    str1 = file.read()
    lst = get_root_s_expr_lst(str1)
    for elm in lst:
        #print("processed element")
        #print(elm)
        #print("="*8)
        result.append(sexpdata.loads(elm))
    return result

"""The types which Variable class might have"""
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
    """convert VarType Enum to their corresponding strings"""
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
    """variable class stores the name and type of variable"""
    def __init__(self,var_name:str,var_type:VarType):
        self.var_name = var_name
        self.var_type = var_type
    def __str__(self):
        return f"Variable({self.var_name},{self.var_type})"
    __repr__ = __str__
"""The types of a message class"""
class MsgType(Enum):
    ENCRYPTED_TERM = 1
    CAT_TERM = 2
    ATOM_TERM = 3
    LTK_TERM = 4
    PUBK_TERM = 5
    PRIVK_TERM = 6
    ##have to add privk forgot to deal with that
class Message:
    """Message class stores the type of the message and the data within a message,
    for ATOM_TERM the msg_data contains just the Variable corresponding to the term
    for CAT_TERM the list of messages in it and similar logic for other datatypes"""
    def __init__(self,msg_type:MsgType,args_arr:Union[List['Message'],Variable]):
        self.msg_type = msg_type
        self.msg_data = args_arr
    def __str__(self):
        return f"Message({self.msg_type},{self.msg_data})"
    def __repr__(self):
        return self.__str__()
"""Marks whether trace is SEND/RECV"""
class SendRecv(Enum):
    SEND_TRACE = 1
    RECV_TRACE = 2
class Role:
    """Stores all terms within a role"""
    def __init__(self,role_name:str,var_dict:Dict[str,Variable],msg_trace:List[Tuple[SendRecv,Message]]):
        self.role_name = role_name
        self.var_dict = var_dict
        self.msg_trace = msg_trace
    def is_valid_var_name(self,var_name:str):
        return (var_name in self.var_dict)
    def get_var_obj(self,var_name:str):
        return self.var_dict[var_name]
    def __str__(self):
        return f"Role({self.role_name},{self.var_dict},{self.msg_trace})"
    def __repr__(self):
        return self.__str__()
class Protocol:
    """Stores all the roles involved and the protocol name itself"""
    def __init__(self,roles_arr:List[Role],prot_name:str,basic_str:str):
        self.roles_arr = roles_arr
        self.prot_name = prot_name
        self.basic_str = basic_str
    def is_valid_role_name(self,role_name:str):
        return (role_name in map(lambda role_obj:role_obj.role_name,self.roles_arr))
    def get_role_obj(self,role_name:str):
        for role_obj in self.roles_arr:
            if role_name == role_obj.role_name:
                return role_obj
        return None
    def __str__(self):
        return f"Protocol(\n{self.roles_arr},\n{self.prot_name},\n{self.basic_str})"
    def __repr__(self):
        return self.__str__()
class Strand:
    """Stores the variable mapping between role and skeleton specified in defstrand clause"""
    #i think trace len is being ignored for now?
    def __init__(self,role_name:str,trace_len:int,var_map:Dict[str,str]):
        self.role_name = role_name
        self.trace_len = trace_len
        self.var_map = var_map
    def __str__(self):
        return f"Strand({self.role_name},{self.trace_len},\n{self.var_map})"
    def __repr__(self):
        return self.__str__()
class ConstrType(Enum):
    """Enum for types of constraints"""
    UNIQ_ORIG = 0
    NON_ORIG = 1
class Constraint:
    """Refers to an individual constraint of type either non-orig/uniq-orig refering to some message"""
    def __init__(self,constr_type:ConstrType,msg_on_constr:Message):
        self.constr_type = constr_type
        self.msg_on_constr = msg_on_constr
    def __str__(self):
        return f"Constraint({self.constr_type},{self.msg_on_constr})"
    def __repr__(self):
        return self.__str__()
class Skeleton:
    """Stores all the constraints and variable map defined in the defskeleton clause"""
    def __init__(self,prot_name:str,var_dict:Dict[str,Variable],strand_list:List[Strand],orig_constr:List[Constraint]):
        self.prot_name = prot_name
        self.var_dict = var_dict
        self.strand_list = strand_list
        self.orig_constr = orig_constr
    def __str__(self):
        return f"Skeleton({self.prot_name},\n{self.var_dict},\n{self.strand_list},\n{self.orig_constr})"
    def __repr__(self):
        return self.__str__()
class ParseException(Exception):
    """parse exception used to signal an exception in lot of the transcribing functions"""
    def __init__(self,message):
        self.message = message
        super().__init__(message)

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

def s_expr_instead_of_str(expected_str:str,s_expr) -> ParseException:
    """function to generate a common exception where there should have been a simple string but found an s-expression instead"""
    return ParseException(f"Expected '{expected_str}' string not an s expression {str(s_expr)} with type {type(s_expr)}")

def unexpected_str_error(expected_str:str,unexpected_str:str) -> ParseException:
    """function to generate a common exception where the s_expr contains an unexpected string 
    Ex: expected defprotocol at beginning of protocol but saw something else"""
    return ParseException(f"Expected '{expected_str}' string at beginning of s expression not {unexpected_str}")


def get_var(var_name_str:str,variable_dict:Dict[str,Variable]) -> Variable:
    """returns the variable corresponding to a variable name, if not present raise an exception"""
    if var_name_str not in variable_dict:
        raise ParseException(f"Unknown Variable Name {var_name_str} known variables are {variable_dict.keys()}")
    return variable_dict[var_name_str]

def is_symbol_type(symbl) -> bool:
    return type(symbl) == sexpdata.Symbol

def match_type_and_str(s_expr,expected_str:str) -> None:
    """helper function to check that an s-expr is a specific string like defprotocol"""
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(expected_str,s_expr)
    if str(s_expr) != expected_str:
        raise unexpected_str_error(expected_str,str(s_expr))


def match_var_type(var:Variable,expected_var_type:VarType) -> None:
    """generates exception when a variable is not a correct type, 
    example when encrypting a key cannot be a  name"""
    if var.var_type != expected_var_type:
        raise ParseException(f"Expected var type = {vartype_to_str(expected_var_type)} but got {vartype_to_str(var.var_type)}")

def get_str_from_symbol(s_expr:sexpdata.Symbol,data_name:str) -> str:
    """simply gets the string from an s-expr"""
    if not is_symbol_type(s_expr):
        raise s_expr_instead_of_str(data_name,s_expr)
    return str(s_expr)
def get_int_from_s_expr(s_expr,data_name:str) -> str:
    """simply gets the int from an s-expr"""
    if type(s_expr) != int:
        raise ParseException(f"Expected type int here not type {type(s_expr)}")
    return s_expr
def parse_vars_list(s_expr,var_dict) -> None:
    """this functions parses a list of variables parses expressions 
    like (a b name) found inside a vars clause"""
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
    """this function parses the vars clause of the 
    form (vars (a b name) (n1 n2 text))"""
    var_dict = {}
    if len(s_expr) < 2:
        raise ParseException(f"Expected 'vars' and variables list in the s expression but length of s expression is = {len(s_expr)}")
    match_type_and_str(s_expr[0],VARS_STR)
    for elm in s_expr[1:]:
        parse_vars_list(elm,var_dict)
    return var_dict

#parses encrypted term and cat term for now
def parse_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """this function parses a message term, either just a base term 
    like a variable name, ex n1 in (enc n1 (pubk b))"""
    if type(s_expr) == sexpdata.Symbol:
        var_name = get_str_from_symbol(s_expr,"var name")
        var = get_var(var_name,var_dict)
        return Message(MsgType.ATOM_TERM,var)
    if len(s_expr) < 1:
        raise ParseException(f"empty s-expr cannot be a term")
    
def parse_ltk(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """this function parses the ltk clause of the form (ltk name1 name2)"""
    if len(s_expr) != 3:
        raise ParseException(f"Expected s-expr of length 3 ltk name1 name2 but length is {len(s_expr)}")
    match_type_and_str(s_expr[0],LTK_STR)
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
    """this function parses the pubk clause of the form (pubk name1)"""
    if len(s_expr) != 2:
        raise ParseException(f"Expected s-expr of length 2 pibk name but length is {len(s_expr)} s_expr is {str(s_expr)}")
    match_type_and_str(s_expr[0],PUBK_STR)
    str_name = get_str_from_symbol(s_expr[1],"name in pubk")
    name = get_var(str_name,var_dict)
    if name.var_type != VarType.NAME:
        raise ParseException(f"Expected variable type {vartype_to_str(VarType.NAME)} got {vartype_to_str(name.var_type)}")
    name_term = Message(MsgType.ATOM_TERM,name)
    return Message(MsgType.PUBK_TERM,[name_term])
def parse_privk(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """this function parses the privk clause of the form (privk name1) """
    if len(s_expr) != 2:
        raise ParseException(f"Expected s-expr of length 2 privk, name but length is {len(s_expr)} s_expr is {str(s_expr)}")
    match_type_and_str(s_expr[0],PRIVK_STR)
    str_name = get_str_from_symbol(s_expr[1],"name in privk")
    name = get_var(str_name,var_dict)
    if name.var_type != VarType.NAME:
        raise ParseException(f"Expected varaible type {vartype_to_str(VarType.NAME)} got {vartype_to_str(name.var_type)}")
    name_term = Message(MsgType.ATOM_TERM,name)
    return Message(MsgType.PRIVK_TERM,[name_term])    
def is_valid_key(msg:Message) -> bool:
    """checks if a message term is a valid key, needed to check if can encrypt using this"""
    if msg.msg_type in [MsgType.PUBK_TERM,MsgType.LTK_TERM]:
        return True
    if msg.msg_type == MsgType.ATOM_TERM and msg.msg_data.var_type in [VarType.AKEY,VarType.SKEY]:
        return True
    return False
def parse_enc_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """parses an encrypted term like (enc n1 n2 (pubk a))"""
    if len(s_expr) < 3:
        raise ParseException(f"Expected atleast three terms enc,message and encryption key")
    data_terms_lst = [parse_term(t,var_dict) for t in s_expr[1:-1]]
    key_term_expr = s_expr[-1]
    key_term = parse_term(key_term_expr,var_dict)
    if not is_valid_key(key_term):
        raise ParseException(f"Expected term of type key but got {str(s_expr)}")
    data_terms_lst.append(key_term)
    return Message(MsgType.ENCRYPTED_TERM,data_terms_lst)

#condenses any nested cat term not used any example yet will impl later
def condense_cat_term(msg_list:List[Message]) -> Message:
    """TODO: would condednse nested cat terms to use only one concatenated messages
    exampke (cat n1 (cat n2 n3)) == (cat n1 n2 n3)"""
    pass
def parse_cat_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """parses concatenated terms like (cat a (enc n1 n2 (pubk a))"""
    if len(s_expr) < 1:
        raise ParseException(f"Expected atleast two terms cat and some data")
    data_terms_lst = [parse_term(t,var_dict) for t in s_expr[1:]]
    return Message(MsgType.CAT_TERM,data_terms_lst)

def parse_atom(s_expr:sexpdata.Symbol,var_dict:Dict[str,Variable]) -> Variable:
    """parses an atomic term, consisting of just one variable like 
    n1 where n1 is a variable defined in the vars clause of a role"""
    var_term_name = get_str_from_symbol(s_expr,"message term")
    var_term = get_var(var_term_name,var_dict)
    return var_term
def parse_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """parses any term of either encrypted term,concatenated term,ltk term,pubk term etc."""
    if type(s_expr) == sexpdata.Symbol:
        var_term = parse_atom(s_expr,var_dict)
        return Message(MsgType.ATOM_TERM,var_term)
    if len(s_expr) < 2:
        raise ParseException(f"Since s-expr in message expected enc or cat followed by message term")
    enc_cat_ltk_pubk_str = get_str_from_symbol(s_expr[0],"enc/cat/ltk/pubk")        
    # TODO: Add parsing for privk
    func_dict = {
        ENC_STR  : parse_enc_term,
        CAT_STR  : parse_cat_term,
        LTK_STR  : parse_ltk,
        PUBK_STR : parse_pubk,
        PRIVK_STR: parse_privk
    }
    if enc_cat_ltk_pubk_str not in func_dict:
        raise ParseException(f"Expected s-expr message term to start with enc/cat/pubk/ltk not {enc_cat_ltk_pubk_str}")    
    return func_dict[enc_cat_ltk_pubk_str](s_expr,var_dict)

def parse_indv_trace(s_expr,var_dict) -> Tuple[SendRecv,Message]:
    """parses individual trace present in the trace clause of a role 
    Example: (send (enc (n1 n2 (pubk a))))"""
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
    """parses the trace in a role consisting of a sequence of sends and recieves
    Example : (trace (send (enc n1 (pubk b))) (recv (enc n1 n2 (pubk a))) (send (enc n2 (pubk b))))"""
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
    """parses the role clause present inside a protocol clause 
    Example:(defrole role_name (vars ..) ( trace .. ))"""
    if len(s_expr) != 4:
        raise ParseException(f"Expected 'defrole',role_name,variables list and trace of sends and receives but length of s expr is {len(s_expr)}")
    match_type_and_str(s_expr[0],DEF_ROLE_STR)
    role_name = get_str_from_symbol(s_expr[1],"role name")
    var_dict = parse_vars_clause(s_expr[2])
    msg_trace = parse_trace(s_expr[3],var_dict)

    return Role(role_name,var_dict,msg_trace)    

def parse_protocol(s_expr) -> Protocol:
    """parses the whole protocol clause which includes multiple role clauses in it 
    (defprotocol prot_name basic (defrole .. ) (defrole .. ))"""
    if len(s_expr) < 4:
        raise ParseException(f"Expected 'defprotocol',protocol name,'basic' and atleast one role but size of s_expr is = {len(s_expr)}")
    match_type_and_str(s_expr[0],DEF_PROT_STR)

    prot_name = get_str_from_symbol(s_expr[1],"protocol name")
    match_type_and_str(s_expr[2],BASIC_STR)
    
    return Protocol([parse_role(role_expr) for role_expr in s_expr[3:]],prot_name,BASIC_STR)    

"""
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
"""
def parse_var_mapping(s_expr,var_map_dict:Dict[str,str],role_obj:Role):
    """parses the variable mapping in a defstrand clause example (a b) where 
    a is a variable in the role b is a variable in the skeleton,function also 
    checks that the variable names are valid"""
    if len(s_expr) != 2:
        raise ParseException("Expected skeleton variable name,role variable name")
    skelet_var_name = get_str_from_symbol(s_expr[0],"skeleton var name")
    ##should add check for if role names and variable names re valid as well
    role_var_name = get_str_from_symbol(s_expr[1],"role var name")
    if not role_obj.is_valid_var_name(role_var_name):
        raise ParseException(f"Varible name '{role_var_name}' and type '{type(role_var_name)}' not present in role declaration '{role_obj.role_name}' which has variable list '{list(role_obj.var_dict.keys())}' '{list(map(type,list(role_obj.var_dict.keys())))}'")
    if (skelet_var_name in var_map_dict):
        raise ParseException(f"Repeated variable name {skelet_var_name} in defstrand clause")
    var_map_dict[skelet_var_name] = role_var_name
def parse_strand(s_expr,prot_obj:Protocol) -> Strand:
    """parses the strand clause of the form (defstrand role_name trace_len (var1 var2) ...)"""
    if len(s_expr) < 4:
        raise ParseException("Expected defstrand,role_name,strand len?,variable mappings")
    match_type_and_str(s_expr[0],DEF_STRAND_STR)
    ##should add check for if role names and variable names are valid as well
    role_name = get_str_from_symbol(s_expr[1],"role name")
    if not prot_obj.is_valid_role_name(role_name):
        raise ParseException(f"Role Name {role_name} has not been declared in defprotocol clause")
    role_obj = prot_obj.get_role_obj(role_name)
    trace_len = get_int_from_s_expr(s_expr[2],"trace length")

    var_map_dict = {}
    for elm in s_expr[3:]:
        parse_var_mapping(elm,var_map_dict,role_obj)
    return Strand(role_name,trace_len,var_map_dict)    
#only handles parsing atom terms,pubk,privk,ltk as examples
#doesn't handle parsing cat,enc
def parse_base_term(s_expr,var_dict:Dict[str,Variable]) -> Message:
    """parses only base terms like a variable name,public key,private key,
    long term key. Not concatenated or encrypted terms, used to restrict what
    terms are used for non-orig and uniq-orig"""
    if type(s_expr) == sexpdata.Symbol:
        var_term = parse_atom(s_expr,var_dict)  
        return Message(MsgType.ATOM_TERM,var_term)
    if len(s_expr) == 0:
        raise ParseException(f"Empty s-expression expected ltk,pubk,privk clause")
    clause_type = get_str_from_symbol(s_expr[0],"pubk/privk/ltk")
    if clause_type == PUBK_STR:
        return parse_pubk(s_expr,var_dict)
    elif clause_type == PRIVK_STR:
        return parse_privk(s_expr,var_dict)
    elif clause_type == LTK_STR:
        return parse_ltk(s_expr,var_dict)
    else:
        raise ParseException(f"Unexpected clause_type {clause_type} expected pubk/privk/ltk")
def parse_non_orig(s_expr,var_dict:Dict[str,Variable],constr_lst:List[Constraint]):
    """parse non orig clause of the form (non-orig term1 term2 ...)"""
    if len(s_expr) < 2:
        raise ParseException("expected non-orig and variable clause")
    match_type_and_str(s_expr[0],NON_ORIG_STR)
    for elm in s_expr[1:]:
        cur_base_term = parse_base_term(elm,var_dict)
        cur_constr = Constraint(ConstrType.NON_ORIG,cur_base_term)
        constr_lst.append(cur_constr)

def parse_uniq_orig(s_expr,var_dict:Dict[str,Variable],constr_list:List[Constraint]):
    """parse uniq-orig clause of the form (uniq-orig term1 term2 ...)"""
    if len(s_expr) < 2:
        raise ParseException("expected non-orig and variable clause")
    match_type_and_str(s_expr[0],UNIQ_ORIG_STR)
    for elm in s_expr[1:]:
        cur_base_term = parse_base_term(elm,var_dict)
        cur_constr = Constraint(ConstrType.UNIQ_ORIG,cur_base_term)
        constr_list.append(cur_constr)

def parse_skeleton(s_expr,prot_obj:Protocol) -> Skeleton: """parses a skeleton clause containing the variable declrations, strand declarations,
    non-orig and uniq-orig constraints 
    Ex: (defskeleton (vars ...) (defstrand ...) (non-orig ..) ..)"""
    if type(s_expr) == sexpdata.Symbol:
        raise ParseException("Expected s expression not string literal")
    if len(s_expr) == 1:
        raise ParseException("Empty s expression expected defskeleton")
    match_type_and_str(s_expr[0],DEF_SKEL_STR)
    prot_name = get_str_from_symbol(s_expr[1],"protocol name")
    vars_dict = parse_vars_clause(s_expr[2])

    constraints_lst = []
    strand_arr = [] 

    for sub_expr in s_expr[3:]:
        if type(s_expr) == sexpdata.Symbol:
            raise ParseException("Expected s-expressions not basic string")
        clasue_type = get_str_from_symbol(sub_expr[0],"clause type")
        if clasue_type == DEF_STRAND_STR:
            cur_strand = parse_strand(sub_expr,prot_obj)
            strand_arr.append(cur_strand)
        elif clasue_type == NON_ORIG_STR:
            parse_non_orig(sub_expr,vars_dict,constraints_lst)
        elif clasue_type == UNIQ_ORIG_STR:
            parse_uniq_orig(sub_expr,vars_dict,constraints_lst)
    return Skeleton(prot_name,vars_dict,strand_arr,constraints_lst)
##TODO: Just wrote _skeleton function also have to test it
def parse_file(s_expr):
    """helper function to handle the cases where the file contains only protocol clause
    or protocol and skeleton clause"""
    if len(s_expr) == 0:
        raise ParseException("Empty S expression expected defprotocol clause")
    if len(s_expr) == 1:
        return parse_protocol(s_expr[0])
    if len(s_expr) == 2:
        prot_obj = parse_protocol(s_expr[0])
        skel_obj = parse_skeleton(s_expr[1],prot_obj)
        return [prot_obj,[skel_obj]]
    if len(s_expr) > 2:
        prot_obj = parse_protocol(s_expr[0])
        skel_obj_arr = []
        for i in range(1,len(s_expr)):
            cur_skel_obj = parse_skeleton(s_expr[i],prot_obj)
            skel_obj_arr.append(cur_skel_obj)
        return [prot_obj,skel_obj_arr]

    
