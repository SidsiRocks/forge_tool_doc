from type_and_helpers import *
import sexpdata


def get_root_s_expr_lst(txt: str):
    """the sexpdata library can only parse one s-expr by itself,multiple
    s-expr must be present as an array or similar,hence this adds a wrapper
    around that to find all s-expr"""
    brkt_count = 0
    brkt_started = False
    prev_indx = 0
    strs_so_far = []
    for indx, chr in enumerate(txt):
        if chr == '(':
            brkt_count += 1
            brkt_started = True
        elif chr == ')':
            brkt_count = brkt_count - 1
        if brkt_count == 0 and brkt_started:
            cur_s_expr_str = txt[prev_indx:(indx + 1)]
            prev_indx = indx + 1
            brkt_started = False
            strs_so_far.append(cur_s_expr_str)
    return strs_so_far


def parse_vars_list(s_expr, var_map: VarMap) -> None:
    """this functions parses a list of variables parses expressions
    like (a b name) found inside a vars clause"""
    if len(s_expr) < 2:
        raise ParseException(
            f"Expected variable name and type not {str(s_expr)}")
    data_type_str = get_str_from_symbol(s_expr[-1], "variable type")
    data_type = str_to_vartype(data_type_str)
    for elm in s_expr[:-1]:
        cur_var_str = get_str_from_symbol(elm, "variable name")
        cur_var = Variable(cur_var_str, data_type)
        if cur_var_str in var_map:
            raise ParseException(f"Repeated variable name {cur_var_str}")
        var_map[cur_var_str] = cur_var


def parse_vars_clause(s_expr) -> VarMap:
    """this function parses the vars clause of the
    form (vars (a b name) (n1 n2 text))"""
    var_map: VarMap = {}
    if len(s_expr) < 2:
        raise ParseException(
            f"Expected 'vars' and variables list in the s expression but length of s expression is = {len(s_expr)}"
        )
    match_type_and_str(s_expr[0], VARS_STR)
    for elm in s_expr[1:]:
        parse_vars_list(elm, var_map)
    return var_map

def parse_skeleton_vars_list(s_expr,role_obj_types:List[str],non_strand_var_map:VarMap,strand_var_map:Dict[str,str]):
    if len(s_expr) < 2:
        raise ParseException(
            f"Expected variable name and type not {str(s_expr)}")
    variable_names = [get_str_from_symbol(variable_name,"variable name")for variable_name in s_expr[:-1]]
    data_type = get_str_from_symbol(s_expr[-1],"variable type")
    msg_data_types = [NAME_STR,TEXT_STR,SKEY_STR,AKEY_STR,MESG_STR]
    is_msg_data = data_type in msg_data_types
    if not is_msg_data and data_type not in role_obj_types:
        raise ParseException(f"Expected variable type to be msg_data like {msg_data_types} or strand types {role_obj_types} not {data_type}")
    for variable_name in variable_names:
        if is_msg_data:
            non_strand_var_map[variable_name] = Variable(variable_name,str_to_vartype(data_type))
        else:
            strand_var_map[variable_name] = data_type

def parse_skeleton_vars_clause(s_expr,prot_obj:Protocol) -> Tuple[VarMap,Dict[str,str]]:
    """this function parses the vars clauses within a defskeleton
    declaration which also includes strands as varaible types
    (vars (a b name) (A role_A) (B role_B) (C role_C))"""
    non_strand_vars_map: VarMap = {}
    strand_vars_map: Dict[str,str] = {}

    if len(s_expr) < 2:
        raise ParseException("")
    match_type_and_str(s_expr[0],VARS_STR)

    role_obj_types = [f"role_{role_obj.role_name}" for role_obj in prot_obj.role_arr]

    for single_declaration in s_expr[1:]:
        parse_skeleton_vars_list(single_declaration,role_obj_types,non_strand_vars_map,strand_vars_map)
    return non_strand_vars_map,strand_vars_map

def parse_key_term(s_expr, var_map: VarMap) -> KeyTerm:
    if is_symbol_type(s_expr):
        var_name = get_str_from_symbol(s_expr, "variable name")
        variable = get_var(var_name, var_map)
        if variable.var_type not in [MsgTypes.AKEY, MsgTypes.SKEY]:
            raise ParseException(
                f"Expected key term to be of type AKEY/SKEY not {variable.var_type}"
            )
        return variable
    key_category = get_str_from_symbol(s_expr[0], "pubk/privk/ltk")
    if key_category not in KEY_CATEGORIES:
        raise ParseException(
            f"Unknown key category {key_category} expected: {KEY_CATEGORIES}")
    if key_category in [PUBK_STR, PRIVK_STR]:
        if len(s_expr) != 2:
            raise ParseException(
                f"Expected exactly 2 terms pubk and agent name actual length {len(s_expr)}"
            )
        agent_name = get_str_from_symbol(s_expr[1], "agent name")
        get_var(agent_name, var_map)
        if key_category == PUBK_STR:
            return PubkTerm(agent_name=agent_name)
        else:
            return PrivkTerm(agent_name=agent_name)
    elif key_category == LTK_STR:
        if len(s_expr) != 3:
            raise ParseException(
                f"Expected exactly 3 terms ltk agent1 name and agent2 name actual length {len(s_expr)}"
            )
        agent1_name = get_str_from_symbol(s_expr[1], "agent name")
        get_var(agent1_name, var_map)
        agent2_name = get_str_from_symbol(s_expr[2], "agent name")
        get_var(agent2_name, var_map)
        return LtkTerm(agent1_name=agent1_name, agent2_name=agent2_name)
    else:
        raise ParseException(
            f"Unrecognised key category {key_category} in {s_expr}")

def parse_seq_term(s_expr,var_dict:VarMap) -> Message:
    if len(s_expr) < 2:
        raise ParseException(f"expected seq keyword and atleast one message term not {s_expr}")
    match_type_and_str(s_expr[0],SEQ_STR)
    data : List[Message] = [parse_message_term(sub_expr,var_dict) for sub_expr in s_expr[1:]]
    non_cat_data : List[NonCatTerm] = []
    #TODO: can add code for condensing cat here as well
    for msg_subterm in data:
        match msg_subterm:
            #TODO: may want to extend message types to incorporate atomic and other classes mybe could be useful when stating seq term
            case Variable(var_name,var_type):
                acceptable_var_types = [MsgTypes.AKEY,MsgTypes.SKEY,MsgTypes.NAME]
                if var_type not in acceptable_var_types:
                    raise ParseException(f"{msg_subterm} type is not in {acceptable_var_types} allowed in seq term")
                non_cat_data.append(msg_subterm)
            case EncTerm(_) | LtkTerm(_) | PubkTerm(_) | PrivkTerm(_):
                non_cat_data.append(msg_subterm)
            case _:
                raise ParseException(f"Expected EncTerm,LtkTerm,PubkTerm,PrivkTermf or seq not {msg_subterm}")
    return SeqTerm(non_cat_data)

def parse_message_term(s_expr, var_dict: VarMap) -> Message:
    if is_symbol_type(s_expr):
        variable_name = get_str_from_symbol(s_expr, "variable name")
        if variable_name not in var_dict and variable_name not in predefined_constants:
            raise ParseException(
                f"unknown variable name {variable_name} not previously declated"
            )
        if variable_name in var_dict:
            return var_dict[variable_name]
        return predefined_constants[variable_name]
    message_category = get_str_from_symbol(s_expr[0], "enc/cat/pubk/privk/ltk")
    if message_category not in MESSAGE_CATEGORIES:
        raise ParseException(
            f"Unkown message category {message_category} expected: {MESSAGE_CATEGORIES}"
        )

    if message_category == ENC_STR:
        if len(s_expr) < 3:
            raise ParseException(
                f"expected at least 3 terms for an s expreesion enc,data,key but length is {len(s_expr)}"
            )
        data = [
            parse_message_term(subterm_sexpr, var_dict)
            for subterm_sexpr in s_expr[1:-1]
        ]
        key = parse_key_term(s_expr[-1], var_dict)
        condensed_data: List[NonCatTerm] = []
        for msg_subterm in data:
            match msg_subterm:
                case CatTerm(cat_data):
                    condensed_data.extend(cat_data)
                case other_subterm:
                    condensed_data.append(other_subterm)
        return EncTerm(data=condensed_data, key=key)
    elif message_category == CAT_STR:
        if len(s_expr) < 2:
            raise ParseException(f"Cannot have empty message")
        data: List[Message] = [
            parse_message_term(subterm_sexp, var_dict)
            for subterm_sexp in s_expr[1:]
        ]
        condensed_data: List[NonCatTerm] = []
        for msg_subterm in data:
            match msg_subterm:
                case CatTerm(cat_data):
                    condensed_data.extend(cat_data)
                case other_subterm:
                    condensed_data.append(other_subterm)
        return CatTerm(data=condensed_data)
    elif message_category == SEQ_STR:
        return parse_seq_term(s_expr,var_dict)
    elif message_category in KEY_CATEGORIES:
        return parse_key_term(s_expr, var_dict)
    else:
        raise ParseException(
            f"unknown message category {message_category} in {s_expr}")


def parse_indv_trace(s_expr, var_map: VarMap) -> IndvTrace:
    """parses individual trace present in the trace clause of a role
    Example: (send (enc (n1 n2 (pubk a))))"""
    if len(s_expr) != 2:
        raise ParseException(
            f"Expected send/recv followed by message as s_expr len(s_expr) is: {len(s_expr)}"
        )
    send_or_recv_str = get_str_from_symbol(s_expr[0], "send/recv")
    if send_or_recv_str != SEND_STR and send_or_recv_str != RECV_STR:
        raise ParseException(
            f"Expected send/recv clause not {send_or_recv_str}")
    ##currently expecting only one s_expr later if sending multiple
    ##messages deal with having cat instead
    trace_type = SendRecv.SEND if send_or_recv_str == SEND_STR else SendRecv.RECV
    return trace_type, parse_message_term(s_expr[1], var_map)


def parse_trace(s_expr, var_map: VarMap) -> MessageTrace:
    """parses the trace in a role consisting of a sequence of sends and recieves
    Example : (trace (send (enc n1 (pubk b))) (recv (enc n1 n2 (pubk a))) (send (enc n2 (pubk b))))"""
    #currently forcing limit of 3 becuase the current racket code seems
    #to have that restriction as well will see what to do with this later
    if len(s_expr) < 3:
        raise ParseException(
            f"Expecred 'trace' and atleast two messages current length of s_expr is: {len(s_expr)}"
        )
    match_type_and_str(s_expr[0], TRACE_STR)
    result = []
    for indv_trace in s_expr[1:]:
        result += [parse_indv_trace(indv_trace, var_map)]
    return result


def parse_role(s_expr) -> Role:
    """parses role clause present in a protocol clause.
    Ex: (defrole role_name (vars (a b name) ..) (trace (send ...) (recv ...)))"""
    if len(s_expr) != 4:
        raise ParseException(
            f"Expected 'defrole',role_name,variables list and trace of sends and receives but length of s expr is {len(s_expr)}"
        )
    match_type_and_str(s_expr[0], DEF_ROLE_STR)
    role_name = get_str_from_symbol(s_expr[1], "role name")
    var_map = parse_vars_clause(s_expr[2])
    msg_trace = parse_trace(s_expr[3], var_map)

    return Role(role_name=role_name, var_map=var_map, trace=msg_trace)


def parse_protocol(s_expr) -> Protocol:
    """parses protocol clause used to define protocol for which run
    would be found.
    Ex: (defprotocol prot_name basic (defrole ..) ...)"""
    if len(s_expr) < 4:
        raise ParseException(
            f"Expected 'defprotocol',protocol name,'basic' and atleast one role but size of s_expr is = {len(s_expr)}"
        )
    match_type_and_str(s_expr[0], DEF_PROT_STR)
    protocol_name = get_str_from_symbol(s_expr[1], "protocol name")
    match_type_and_str(s_expr[2], BASIC_STR)
    role_arr = [parse_role(role_expr) for role_expr in s_expr[3:]]
    return Protocol(protocol_name=protocol_name, role_arr=role_arr)

#TODO: have to add checks for types of variables in role and skeleton matching
def parse_var_mapping(s_expr, skeleton_vars_dict: VarMap, role_obj: Role) -> Tuple[str,Variable]:
    """parses variable mapping of the form (strnad-var-name skel-var-name) seen inside defstrand clause."""
    if len(s_expr) != 2:
        raise ParseException(
            f"Exepcted only two symbols in var mapping strand variable name and skeleton variable name"
        )
    skel_var_name = get_str_from_symbol(s_expr[0], "skeleton variable name")
    strand_var_name = get_str_from_symbol(s_expr[1], "strand variable name")
    strand_var = get_var(strand_var_name, role_obj.var_map)
    _ = get_var(skel_var_name, skeleton_vars_dict)
    return skel_var_name, strand_var


def parse_strand(s_expr, prot_obj: Protocol,
                 skeleton_vars_dict: VarMap) -> Strand:
    """parse strand declarations seen in defskeleton clause. Example (defstrand strand-name trace-len (skl-var-1 strand-var-1) (strand-var-2 skel-var-2) ... )"""
    #TODO: Confirm that the order here is correct i.e strand to skeleton
    if len(s_expr) < 4:
        raise ParseException(
            "Expected defstrand,role_name,strand length,variable mappings from strand to skeleton"
        )
    match_type_and_str(s_expr[0], DEF_STRAND_STR)
    role_name = get_str_from_symbol(s_expr[1], "role name")
    #TODO: maybe also check the trace length here?
    trace_len = get_int_from_symbol(s_expr[2], "trace length")
    role_in_prot = prot_obj.role_obj_of_name(role_name)
    if role_in_prot is None:
        raise ParseException(f"no role in protocol with rolename {role_name}")
    #+TODO: check if should reverse order of strand and skeleton here
    skeleton_to_strand_var_map:Dict[str,Variable] = {}
    for elm in s_expr[3:]:
        skel_var_name, strand_var = parse_var_mapping(elm, skeleton_vars_dict,
                                                      role_in_prot)
        skeleton_to_strand_var_map[skel_var_name] = strand_var
    return Strand(role_name=role_name,
                  trace_len=trace_len,
                  skeleton_to_strand_var_map=skeleton_to_strand_var_map)


def parse_base_term(s_expr, var_map: Dict[str, Variable]) -> BaseTerm:
    """parses only base terms like a variable name,public key,private key, long term key. Not concatenated or encrypted terms, used to restrict what terms can be passed in to non-orig and uniq-orig"""
    if type(s_expr) == sexpdata.Symbol:
        var_name = get_str_from_symbol(s_expr, "variable name")
        return get_var(var_name, var_map)
    if len(s_expr) == 0:
        raise ParseException(
            f"Empty s-expression expected ltk,pubk,privk clause")
    clause_type = get_str_from_symbol(s_expr[0], "pubk/privk/ltk")
    if clause_type in [PUBK_STR, PRIVK_STR, LTK_STR]:
        return parse_key_term(s_expr, var_map)
    else:
        raise ParseException(
            f"Unexpected clause_type {clause_type} expected pubk/privk/ltk")


def parse_non_orig(s_expr, skeleton_vars_dict: VarMap) -> NonOrig:
    """parse non orig clause of the form (non-orig term1 term2 ...)"""
    if len(s_expr) < 2:
        raise ParseException(
            "expected non-orig and variable clause in the s-expr")
    match_type_and_str(s_expr[0], NON_ORIG_STR)
    base_terms = [
        parse_base_term(s_expr, skeleton_vars_dict) for s_expr in s_expr[1:]
    ]
    return NonOrig(terms=base_terms)


#TODO: Consider returning a list of Uniq Orig each one containing one term instead
def parse_uniq_orig(s_expr, skeleton_vars_dict: VarMap) -> UniqOrig:
    """parse uniq orig clause of the form (uniq-orig term1 term2 ...)"""
    if len(s_expr) < 2:
        raise ParseException(
            "expected non-orig and variable clause in the s-expr")
    match_type_and_str(s_expr[0], UNIQ_ORIG_STR)
    base_terms = [
        parse_base_term(s_expr, skeleton_vars_dict) for s_expr in s_expr[1:]
    ]
    return UniqOrig(terms=base_terms)

#TODO: currently no need to write not eq constraint on strand vars so only non
# strand var map is enough
def parse_not_eq(s_expr,skeleton_vars_dict:VarMap) -> NotEqConstraint:
    if len(s_expr) != 3:
        raise ParseException(f"expected not-eq and two message terms not {s_expr}")
    match_type_and_str(s_expr[0],NOT_EQ_STR)
    term1 = parse_base_term(s_expr[1],skeleton_vars_dict)
    term2 = parse_base_term(s_expr[2],skeleton_vars_dict)
    return NotEqConstraint(term1,term2)

def parse_indv_send_recv_constraint(s_expr,non_strand_vars_map:VarMap,strand_vars_map:Dict[str,str]) -> IndvSendRecvInConstraint:
    send_or_recv = get_str_from_symbol(s_expr[0],"send or recv type of constraint")
    if send_or_recv not in [SEND_FROM_STR,RECV_BY_STR]:
        raise ParseException(f"expected {SEND_FROM_STR} or {RECV_BY_STR} to denote send or recv here not {send_or_recv}")

    trace_type = SendRecv.SEND if send_or_recv == SEND_FROM_STR else SendRecv.RECV
    strand_name = get_str_from_symbol(s_expr[1],"strand name sending/receiving the message")
    if strand_name not in strand_vars_map:
        raise ParseException(f"expected {strand_name} to be in the list of strand variables in {list(strand_vars_map.keys())}")
    message_term = parse_message_term(s_expr[2],non_strand_vars_map)
    return IndvSendRecvInConstraint(trace_type,strand_name,message_term)

def parse_trace_constraint(s_expr,non_strand_vars_map:VarMap,strand_vars_map:Dict[str,str]) -> TraceConstraint:
    if len(s_expr) < 3:
        raise ParseException(f"expected {DEF_TRACE_STR} trace_name and a non empty trace")
    match_type_and_str(s_expr[0],DEF_TRACE_STR)
    trace_name = get_str_from_symbol(s_expr[1],"trace name")
    msg_trace = [parse_indv_send_recv_constraint(indv_trace,non_strand_vars_map,strand_vars_map) for indv_trace in s_expr[2:]]
    return TraceConstraint(msg_trace,trace_name)

#TODO: think about making list array naming consistent
def parse_skeleton(s_expr, prot_obj: Protocol) -> Skeleton:
    """parses skeleton clause used to impose constraint on protocol runs generated
    Ex: (defskeleton prot_name (vars (. .) ..) (defstrand ..) (non-orig ..) (uniq-orig ..))"""
    if type(s_expr) == sexpdata.Symbol:
        raise ParseException(
            "Expected s expression not string literal for skeleton")
    match_type_and_str(s_expr[0], DEF_SKEL_STR)
    protocol_name = get_str_from_symbol(s_expr[1], "protocol name")
    non_strand_vars_map,strand_vars_map = parse_skeleton_vars_clause(s_expr[2],prot_obj)

    constraints_list = []
    for sub_expr in s_expr[3:]:
        if type(s_expr) == sexpdata.Symbol:
            raise ParseException(
                "Expected s-expreesion for clause in skeleton not simple symbol"
            )
        clause_type = get_str_from_symbol(sub_expr[0], "clause type")
        if clause_type == DEF_STRAND_STR:
            cur_strand = parse_strand(sub_expr, prot_obj, non_strand_vars_map)
            constraints_list.append(cur_strand)
        elif clause_type == NON_ORIG_STR:
            constraints_list.append(
                parse_non_orig(sub_expr, non_strand_vars_map))
        elif clause_type == UNIQ_ORIG_STR:
            constraints_list.append(
                parse_uniq_orig(sub_expr, non_strand_vars_map))
        elif clause_type == DEF_TRACE_STR:
            constraints_list.append(
                parse_trace_constraint(sub_expr,non_strand_vars_map,strand_vars_map)
            )
        elif clause_type == NOT_EQ_STR:
            constraints_list.append(
                parse_not_eq(sub_expr,non_strand_vars_map)
            )
        else:
            raise ParseException(f"Expected clause type in {[DEF_STRAND_STR,NON_ORIG_STR,UNIQ_ORIG_STR,DEF_TRACE_STR,NOT_EQ_STR]} not {clause_type}")
    return Skeleton(protocol_name=protocol_name,
                    non_strand_vars_map=non_strand_vars_map,
                    strand_vars_map=strand_vars_map,
                    constraints_list=constraints_list)
