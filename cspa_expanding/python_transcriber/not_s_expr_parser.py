import ply.yacc as yacc
import sys
from collections import defaultdict

import new_transcribe_tuple
from not_s_expr_lexer import tokens
from type_and_helpers import *
from typing import Any
from parser import validate_alt_instance
from pathlib import Path

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

start = 'start'
# start = 'protocol'

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

def p_start(p):
    '''start : protocol instances'''
    p[0] = (p[1],p[2])
def p_protocol(p):
    '''protocol : VAR_NAME COLON stmnt_lst'''
    p[0] = p[1],p[3]

def p_instances(p):
    '''instances : BOUNDS_KEYWORD COLON dictionary'''
    p[0] = p[3]
def p_key_val_num(p):
    '''key_val : VAR_NAME COLON NUM
               | VAR_NAME COLON dictionary'''
    p[0] = (p[1],p[3])
def p_key_val_list(p):
    '''key_val_list : key_val
                    | key_val_list ',' key_val'''
    if len(p) == 4:
        p[1].append(p[3])
        p[0] = p[1]
    else:
        p[0] = [p[1]]
    # if len(p) == 3:
    #     print(f"in key_val_list {len(p)} p[1]:{p[1]} p[2]:{p[2]} p[3]:{p[3]}")
    # else:
    #     print(f"{len(p)} p[1]:{p[1]}")
def p_dictionary(p):
    '''dictionary : '{' key_val_list '}' '''
    p[0] = {key:val for key,val in p[2]}
    print(f"dictionary p[0]:{p[0]}")


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
        print("message list with: ",p[0])
    else:
        p[0] = [p[1]]
        print("base message list with: ",p[0])

def p_nonce(p):
    '''nonce : NONCE_PRE VAR_NAME'''
    p[0] = Variable(p[2],MsgTypes.TEXT)
def p_name(p):
    '''name : NAME_PRE VAR_NAME'''
    p[0] = Variable(p[2],MsgTypes.NAME)

def p_tuple(p):
    '''tuple : '<' msg_list '>' '''
    p[0] = CatTerm(p[2])
def p_func_apply(p):
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
        # TODO: CatTerm should also work here now that we have introduced tuple, will fix and remove type:ignore
        return HashTerm(arg_list[0]) # type: ignore

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
    else:
         print("Syntax error at EOF")


parser = yacc.yacc()

def convert_protocol(prot_name:str,statements:List[Statement]):
    def validate_trace(trace:List[Tuple[SendRecv,Message]]):
        length = len(trace)
        for i in range(1,length):
            cur_send_recv,_ = trace[i]
            prev_send_recv,_ = trace[i-1]
            if cur_send_recv == prev_send_recv:
                raise ParseException(f"In trace\n{trace}\nconsecutive sends and recieves")

    def using_pubk_in_trace(role_name:str,role_trace:List[Tuple[SendRecv,Message]]):
        pubk = PubkTerm(role_name)
        for _,msg in role_trace:
            for subterm in msg.get_subterms():
                match msg:
                    case EncTerm(_,key) | EncTermNoTpl(_,key):
                        if key == pubk:
                            return True
        return False

    def get_role_constraints(time_to_gen_vars:Dict[int,List[str]],var_map:VarMap,role_name:str,role_trace:List[Tuple[SendRecv,Message]]) -> List[RoleConstraints]:
        constraints = []
        pubk_in_trace = using_pubk_in_trace(role_name,role_trace)
        if pubk_in_trace:
            constraints.append(NonOrig([PrivkTerm(role_name)]))

        for _,gen_vars in time_to_gen_vars.items():
            if len(gen_vars) == 0:
                continue
            gen_var_not_in_role = next((var_name for var_name in gen_vars if var_name not in var_map),None)
            if gen_var_not_in_role:
                raise ParseException(f"variable {gen_var_not_in_role} in gen_clause but not in the role itself")
            constraints.append(UniqOrig([var_map[var_name] for var_name in gen_vars]))
            constraints.append(FreshlyGenConstraint([var_map[var_name] for var_name in gen_vars]))
        return constraints

    role_name_to_trace: Dict[str,List[Tuple[SendRecv,Message]]] = defaultdict(list)
    role_name_to_generate: Dict[str,Dict[int,List[str]]] = defaultdict(lambda: defaultdict(list))

    for stmnt in statements:
        role_name_to_trace[stmnt.sender].append((SendRecv.SEND ,stmnt.message))
        sender_indx = len(role_name_to_trace[stmnt.sender]) - 1
        if len(stmnt.gen_list) != 0:
            role_name_to_generate[stmnt.sender][sender_indx].extend(stmnt.gen_list)

        role_name_to_trace[stmnt.reciever].append((SendRecv.RECV,stmnt.message))

    print(f"role_name_to_trace:\n{role_name_to_trace}")
    print(f"role_name_to_generate:\n{role_name_to_generate}")

    role_arr: List[Role] = []
    for role_name,trace in role_name_to_trace.items():
        print("=====Iterator Test=====")
        for _,msg in trace:
            print(msg)
            print(list(msg.get_subterms()))
        print("=======================")

        validate_trace(trace)
        this_role_vars = set()
        for _,msg in trace:
            get_vars_in_msg(msg,this_role_vars)
        var_map = {var.var_name:var for var in this_role_vars}
        # can infer some role constraints from nonces in generated list
        role_constraints = get_role_constraints(role_name_to_generate[role_name],var_map,role_name,trace)
        role_arr.append(Role(role_name,var_map,trace,role_constraints))

    return Protocol(prot_name,role_arr)

def convert_instance(instances_dict:Dict[str,Any]):
    def check_dic_type(instances_dict:Dict[str,Any]) -> Dict[str,int]:
        for key,val in instances_dict.items():
            if not isinstance(val,int):
                raise ParseException(f"for {key} have non int bounds {val}")
        return instances_dict
    def remap_names(instances_dict:Dict[str,int]) -> Dict[str,int]:
        old_new_name = {
            "enc_depth" : "enc-depth",
            "tuple_length": "tuple-length",
            "have_ltks": "have-ltks"
        }
        for old_name,new_name in old_new_name.items():
            if old_name in instances_dict:
                instances_dict[new_name] = instances_dict[old_name]
                del instances_dict[old_name]
        return instances_dict

    instances = []
    for instance_name,instances_bounds in instances_dict.items():
        if isinstance(instances_bounds,int):
            raise ParseException(f"Expected {instance_name} to have an instance as a corresponding value instead of an integer {instances_bounds}")
        instances_bounds = check_dic_type(instances_bounds)
        # TODO: can maybe use import statement for ltk bound or something similar
        have_ltks = bool(instances_bounds["have_ltks"])
        del instances_bounds["have_ltks"]
        remap_names(instances_bounds)
        cur_instances = validate_alt_instance(instances_bounds,prot,instance_name,have_ltks)
        instances.append(cur_instances)
    return instances


def path_rel_to_script(path):
    script_path = Path(__file__).parent
    return str((script_path / path).resolve())


if __name__ == "__main__":
    if len(sys.argv) < 4:
        raise ParseException(f"Expected atleast 2 args file_name and dest_file_name")

    base_file_path = path_rel_to_script("base_with_seq_and_tuple_micro.frg")
    extra_func_file_path = path_rel_to_script("extra_funcs.frg")
    file_name = sys.argv[1]
    extra_forge_file_path = sys.argv[2]
    dest_forge_file_path = sys.argv[3]

    with open(file_name) as file:
        (prot_name,result),instances_dict = parser.parse(file.read())
        print("prot_name: ",prot_name)
        for elm in result:
            print(elm)
        prot = convert_protocol(prot_name,result)
        instances = convert_instance(instances_dict)
        print("converted protocol is: ")
        print(prot)
        print("converted instances: ")
        for instance in instances:
            print(instance)
        with open(dest_forge_file_path,'w') as destination_forge_file:
            transcribe_obj = new_transcribe_tuple.Transcribe_obj(destination_forge_file)
            with open(base_file_path) as base_file:
                transcribe_obj.import_file(base_file)
            with open(extra_func_file_path) as extra_func_file:
                transcribe_obj.import_file(extra_func_file)
            # TODO: same code in main_tuple try to put this in new_transcribe instead
            new_transcribe_tuple.transcribe_protocol(prot,transcribe_obj)
            for instance in instances:
                new_transcribe_tuple.transcribe_instance(instance,prot,transcribe_obj)
            with open(extra_forge_file_path) as extra_forge_file:
                transcribe_obj.import_file(extra_forge_file)

