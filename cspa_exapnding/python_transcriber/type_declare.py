import sexpdata as sexp
from dataclasses import dataclass
from enum import Enum
from typing import List,Tuple,Dict 

class ParseException(Exception):
    """parse exception used to signal an exception occured somewhere while transcribing"""
    pass 

class VarType(Enum):
    NAME = 0
    TEXT = 1
    SKEY = 2
    AKEY = 3
@dataclass
class Variable:
    variable_name: str 
    variable_type: VarType
    def __hash__(self):
        """hash only uses variable_name shouldn't have two variables 
        with same name and different type"""
        return hash(self.variable_name)
    def __eq__(self, other:"Variable"):
        """eq function only check equality of variable name shouldn't have
        two variables with same name and different type"""
        return self.variable_name == other.variable_name
VarDeclarations = List[Variable]
VarMap = Dict[Variable,Variable]

@dataclass
class LtkTerm:
    agent1_name: str 
    agent2_name: str
@dataclass
class PubkTerm:
    agent_name:str
@dataclass
class PrivkTerm:
    agent_name:str
KeyTerm = LtkTerm | PubkTerm | PrivkTerm

@dataclass
class EncTerm:
    data: List["Message"]
    key: KeyTerm
class CatTerm:
    data: List["Message"]
class SendRecv(Enum):
    SEND = 0
    RECV = 1
Message = Variable | EncTerm | CatTerm | KeyTerm
MessageTrace = List[Tuple[SendRecv,Message]]

@dataclass
class Role:
    variable_list: VarDeclarations
    trace:List[MessageTrace]

@dataclass
class Protocol:
    protocol_name: str 
    role_arr: List[Role]

@dataclass
class Strand:
    role_name: str 
    trace_len: int 
    var_map: VarMap

BaseTerm = Variable | KeyTerm
@dataclass
class NonOrig:
    terms: List[BaseTerm]
@dataclass
class UniqOrig:
    terms: List[BaseTerm]
Constraint = Strand | NonOrig | UniqOrig

@dataclass
class Skeleton:
    protocol_name: str 
    vars_list: VarDeclarations 
    constraints_list: List[Constraint]
