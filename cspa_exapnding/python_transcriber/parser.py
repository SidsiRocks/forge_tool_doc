from type_and_helpers import *
import sexpdata

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

def parse_vars_list(s_expr,var_map:VarMap) -> None:
    """this functions parses a list of variables parses expressions
    like (a b name) found inside a vars clause"""
    if len(s_expr) < 2:
        raise ParseException(f"Expected variable name and type not {str(s_expr)}")
    data_type_str = get_str_from_symbol(s_expr[-1],"variable type")
    data_type = str_to_vartype(data_type_str)
    for elm in s_expr[:-1]:
        cur_var_str = get_str_from_symbol(elm,"variable name")
        cur_var = Variable(cur_var_str,data_type)
        if cur_var in var_map:
            raise ParseException(f"Repeated variable name {cur_var_str}")
        var_map[cur_var_str] = cur_var

def parse_vars_clause(s_expr) -> VarMap:
    """this function parses the vars clause of the
    form (vars (a b name) (n1 n2 text))"""
    var_map : VarMap = {}
    if len(s_expr) < 2:
        raise ParseException(f"Expected 'vars' and variables list in the s expression but length of s expression is = {len(s_expr)}")
    match_type_and_str(s_expr[0],VARS_STR)
    for elm in s_expr[1:]:
        parse_vars_list(elm,var_map)
    return var_map
def parse_key_term(s_expr,var_map:VarMap) -> KeyTerm:
    if is_symbol_type(s_expr):
        var_name = get_str_from_symbol(s_expr,"variable name")
        variable = get_var(var_name,var_map)
        if variable.variable_type not in [VarType.AKEY,VarType.SKEY]:
            raise ParseException(f"Expected key term to be of type AKEY/SKEY not {variable.variable_type}")
        return variable
    key_category = get_str_from_symbol(s_expr[0],"pubk/privk/ltk")
    if key_category not in KEY_CATEGORIES:
        raise ParseException(f"Unknown key category {key_category} expected: {KEY_CATEGORIES}")
    if key_category in [PUBK_STR,PRIVK_STR]:
        if len(s_expr) != 2:
            raise ParseException(f"Expected exactly 2 terms pubk and agent name actual length {len(s_expr)}")
        agent_name = get_str_from_symbol(s_expr[1],"agent name")
        get_var(agent_name,var_map)
        if key_category == PUBK_STR:
            return PubkTerm(agent_name=agent_name)
        else:
            return PrivkTerm(agent_name=agent_name)
    elif key_category == LTK_STR:
        if len(s_expr) != 3:
            raise ParseException(f"Expected exactly 3 terms ltk agent1 name and agent2 name actual length {len(s_expr)}")
        agent1_name = get_str_from_symbol(s_expr[1],"agent name")
        get_var(agent1_name,var_map)
        agent2_name = get_str_from_symbol(s_expr[2],"agent name")
        get_var(agent2_name,var_map)
        return LtkTerm(agent1_name=agent1_name,agent2_name=agent2_name)
    else:
        raise ParseException(f"Unrecognised key category {key_category} in {s_expr}")
def parse_message_term(s_expr,var_dict:VarMap) -> Message:
    if is_symbol_type(s_expr):
        variable_name = get_str_from_symbol(s_expr,"variable name")
        if variable_name not in var_dict:
            raise ParseException(f"unknown variable name {variable_name} not previously declated")
        return var_dict[variable_name]
    message_category = get_str_from_symbol(s_expr[0],"enc/cat/pubk/privk/ltk")
    if message_category not in MESSAGE_CATEGORIES:
        raise ParseException(f"Unkown message category {message_category} expected: {MESSAGE_CATEGORIES}")

    if message_category == ENC_STR:
        if len(s_expr) < 3:
            raise ParseException(f"expected at least 3 terms for an s expreesion enc,data,key but length is {len(s_expr)}")
        data = [parse_message_term(subterm_sexpr,var_dict) for subterm_sexpr in s_expr[1:-1]]
        key = parse_key_term(s_expr[-1],var_dict)
        condensed_data:List[Message] = []
        for msg_subterm in data:
            match msg_subterm:
                case CatTerm(data=data):
                    condensed_data.extend(data)
                case other_subterm:
                    condensed_data.append(other_subterm)
        return EncTerm(data=condensed_data,key=key)
    elif message_category == CAT_STR:
        if len(s_expr) < 2:
            raise ParseException(f"Cannot have empty message")
        data:List[Message] = [parse_message_term(subterm_sexp,var_dict) for subterm_sexp in s_expr[1:]]
        condensed_data:List[Message] = []
        for msg_subterm in data:
            match msg_subterm:
                case CatTerm(data=data):
                    condensed_data.extend(data)
                case other_subterm:
                    condensed_data.append(other_subterm)
        return CatTerm(data=condensed_data)
    elif message_category in KEY_CATEGORIES:
        return parse_key_term(s_expr,var_dict)
    else:
        raise ParseException(f"unknown message category {message_category} in {s_expr}")
def parse_indv_trace(s_expr,var_map:VarMap) -> IndvTrace:
    """parses individual trace present in the trace clause of a role
    Example: (send (enc (n1 n2 (pubk a))))"""
    if len(s_expr) != 2:
        raise ParseException(f"Expected send/recv followed by message as s_expr len(s_expr) is: {len(s_expr)}")
    send_or_recv_str = get_str_from_symbol(s_expr[0],"send/recv")
    if send_or_recv_str != SEND_STR and send_or_recv_str != RECV_STR:
        raise ParseException(f"Expected send/recv clause not {send_or_recv_str}")
    ##currently expecting only one s_expr later if sending multiple
    ##messages deal with having cat instead
    trace_type = SendRecv.SEND if send_or_recv_str == SEND_STR else SendRecv.RECV
    return trace_type,parse_message_term(s_expr[1],var_map)

def parse_trace(s_expr,var_map:VarMap) -> MessageTrace:
    """parses the trace in a role consisting of a sequence of sends and recieves
    Example : (trace (send (enc n1 (pubk b))) (recv (enc n1 n2 (pubk a))) (send (enc n2 (pubk b))))"""
    #currently forcing limit of 3 becuase the current racket code seems
    #to have that restriction as well will see what to do with this later
    if len(s_expr) < 3:
        raise ParseException(f"Expecred 'trace' and atleast two messages current length of s_expr is: {len(s_expr)}")
    match_type_and_str(s_expr[0],TRACE_STR)
    result = []
    for indv_trace in s_expr[1:]:
        result += [parse_indv_trace(indv_trace,var_map)]
    return result

def parse_role(s_expr) -> Role:
    if len(s_expr) != 4:
        raise ParseException(f"Expected 'defrole',role_name,variables list and trace of sends and receives but length of s expr is {len(s_expr)}")
    match_type_and_str(s_expr[0],DEF_ROLE_STR)
    role_name = get_str_from_symbol(s_expr[1],"role name")
    var_map = parse_vars_clause(s_expr[2])
    msg_trace = parse_trace(s_expr[3],var_map)

    return Role(role_name=role_name,var_map=var_map,trace=msg_trace)

def parse_protocol(s_expr) -> Protocol:
    if len(s_expr) < 4:
        raise ParseException(f"Expected 'defprotocol',protocol name,'basic' and atleast one role but size of s_expr is = {len(s_expr)}")
    match_type_and_str(s_expr[0],DEF_PROT_STR)
    protocol_name = get_str_from_symbol(s_expr[1],"protocol name")
    match_type_and_str(s_expr[2],BASIC_STR)
    role_arr = [parse_role(role_expr) for role_expr in s_expr[3:]]
    return Protocol(protocol_name=protocol_name,role_arr=role_arr)
