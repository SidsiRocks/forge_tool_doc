from reader import *
from typing import *
import io
space_str = " "*4

ENC_MSG_STR = "enc"
CAT_MSG_STR = "cat"
ATOM_MSG_STR= "atom"
LTK_MSG_STR = "ltk"
PUBK_MSG_STR= "pubk"
PRIVK_MSG_STR="privk"
def msg_type_to_str(msg_type:MsgType):
    f"""Convert the msg type enum values to corresponding 
    strings seen in the racket code example 
    {MsgType.ATOM_TERM} -> {ATOM_MSG_STR}"""
    msg_type_to_str_dict = {
        MsgType.ATOM_TERM : ATOM_MSG_STR,
        MsgType.ENCRYPTED_TERM: ENC_MSG_STR,
        MsgType.CAT_TERM: CAT_MSG_STR,
        MsgType.LTK_TERM: LTK_MSG_STR,
        MsgType.PUBK_TERM: PUBK_MSG_STR,
        MsgType.PRIVK_TERM: PRIVK_MSG_STR
    }
    return msg_type_to_str_dict[msg_type]

def append_file(org_file:io.TextIOWrapper,new_file:io.TextIOWrapper):
    """appends the content of the org_file to the new_file line by line,
    useful as currently copying the base.frg file into the generated forge
    file for the protocol(couldn't find import in forge)"""
    for line in org_file:
        new_file.write(line)
def transcribe_prot(prot_obj:Protocol,file:io.TextIOWrapper):
    """Function to transcribe the protocol object returned by the parser
    contains nested functions to parse sub components like roles,signatures"""

    #to ensure human readability nested code needs to have correct level of 
    #indentation the space_lvl variable keeps track of the current level of 
    #indetnation and the print_to_file function adds the indentation along
    #with text passed as argument
    space_lvl = 0
    #when generating temporary variables to be used in quantification predicates
    # ex: some atom5,atom6 : t0.data { t0.data = atom5 + atom6}
    #need distinct number suffix not previously used msg_num_avl stores the last
    #used number suffix
    msg_num_avl = 0 
    def get_msg_num():
        """returns fresh number to used as a suffix to a quantification variable"""
        nonlocal msg_num_avl
        msg_num_avl += 1
        return msg_num_avl
    def start_block():
        nonlocal space_lvl 
        space_lvl += 1
    def end_block():
        nonlocal space_lvl 
        space_lvl -= 1
    def print_to_file(txt:str,add_space = True):
        """helper function to print txt argument with correct level of indentation
        into generated file, add_space = True adds indentation, add_space = False
        does not"""
        if add_space:
            print(space_lvl*space_str,end="",file=file)
        print(txt,end="",file=file)
    def transcribe_role_vars_to_sig(role_obj:Role,role_sig_name:str):
        """transcribes role object in racket file to corresponding sig (signature
        with name role_sig_name and fields corresponding to variable declaration 
        in var clause) in generated racket file"""
        print_to_file(f"sig {role_sig_name} extends strand{{\n")
        start_block()
        item_lst = list(role_obj.var_dict.items())
        for var_name,var in item_lst[:-1]:
            print_to_file(f"{role_sig_name}_{var_name}: one {vartype_to_str(var.var_type)},\n")
        var_name,var = item_lst[-1]
        print_to_file(f"{role_sig_name}_{var_name}: one {vartype_to_str(var.var_type)}\n")
        end_block()
        print_to_file(f"}}\n")
    def transcribe_timeslot_msg(arbit_role_name:str,msg_trace:List[Tuple[SendRecv,Message]],role_sig_name:str):
        """transcribing the trace in a role to the corresponding constraints in exec_pred_role_name predicate
        so that each timeslot contains the correct data for that point in the agent's role"""
        def get_msg_var_name(msg_obj:Message):
            """helper function to get_msg_num, adds a prefix corresponding to the type of
            the variable when generating variable name for quantification"""
            cur_num = str(get_msg_num())
            return msg_type_to_str(msg_obj.msg_type)+cur_num
        def write_msg_constraint(msg_obj:Message,msg_var_name:str,arbit_role_name:str,role_sig_name:str,time_indx:int):
            """for a particular message in the trace write appropiate constraints for the timeslot 
            it belongs to"""
            def transcribe_key_term(msg_obj:Message,arbit_role_name:str):
                if msg_obj.msg_type == MsgType.LTK_TERM:
                    name_var_1,name_var_2 = msg_obj.msg_data
                    return f"getLTK[{name_var_1.msg_data.var_name},{name_var_2.msg_data.var_name}]"
                elif msg_obj.msg_type == MsgType.PUBK_TERM:
                    name_var = msg_obj.msg_data[0].msg_data                
                    #print_to_file(f"((Keypairs.owners).({arbit_role_name}.{role_sig_name}_{name_var.var_name})).(KeyPairs.pairs) = {msg_var_name}\n")
                    return f"getPUBK[{arbit_role_name}.{role_sig_name}_{name_var.var_name}]"
                elif msg_obj.msg_type == MsgType.PRIVK_TERM:
                    name_var = msg_obj.msg_data[0].msg_data
                    return f"getPRIVK[{arbit_role_name}.{role_sig_name}_{name_var.var_name}]"
                raise ParseException(f"transcribe_key_term expected either LTK,PUBK or PRIVK not {msg_obj.msg_type}")
            def write_cat_constraint(msg_obj:Message,msg_var_name:str,arbit_role_name:str,time_indx:int):
                """write constraints for an object of cat type"""
                def write_indices_header(msg_var_name:str,num_terms_int_cat:int):
                    """constraints for subterm requires existential quantification, this function adds
                    the code required for that"""
                    print_to_file(f"inds[{msg_var_name}] = ")
                    for i in range(num_terms_int_cat - 1):
                        print_to_file(f"{i} + ",add_space=False)
                    print_to_file(f"{num_terms_int_cat-1}\n",add_space=False)
                def write_sub_term_header(msg_var_name,cat_sub_term_names:List[str]):
                    """constraints for subterm requires existential quantification, this function adds
                    the code required for that"""
                    print_to_file(f"some ")
                    for sub_term_name in cat_sub_term_names[:-1]:
                        print_to_file(f"{sub_term_name},",add_space=False)
                    print_to_file(f"{cat_sub_term_names[-1]} : elems[{msg_var_name}] {{\n",add_space=False)
                    start_block()
                def write_sub_term_footer():
                    """closing the existential quantification block of code"""
                    end_block()
                    print_to_file(f"}}\n")
                ##along with cat term if message has only one term have to deal with that
                def write_data_constraint(msg_var_name:str,cat_sub_term_names:List[str]):
                    """writes the constraint for each subterm belonging to the cat term"""
                    for indx,sub_term_name in enumerate(cat_sub_term_names):
                        print_to_file(f"({msg_var_name})[{indx}] = {sub_term_name}\n")
                cat_sub_term_names = [get_msg_var_name(msg_sub_term) for msg_sub_term in msg_obj.msg_data]
                write_indices_header(msg_var_name,len(cat_sub_term_names))
                write_sub_term_header(msg_var_name,cat_sub_term_names)    
                write_data_constraint(msg_var_name,cat_sub_term_names)
                for sub_term_name,sub_term_obj in zip(cat_sub_term_names,msg_obj.msg_data):
                    write_msg_constraint(sub_term_obj,sub_term_name,arbit_role_name,role_sig_name,time_indx)
                write_sub_term_footer()
            def write_enc_constraint(msg_obj:Message,msg_var_name:str,arbit_role_name:str,time_indx:int):
                """writes the constraint for encrypted terms similar to cat with extra restriction on
                plaintext and encryptionKey"""
                def write_enc_header():
                    get_msg_var_name(msg_obj)
                def write_enc_footer():
                    pass

                key_term = msg_obj.msg_data[-1]                
                transcribed_key = transcribe_key_term(key_term,arbit_role_name)

                print_to_file(f"{msg_var_name} in Ciphertext\n") #ensuring even if key is not known the term is still in Ciphertext
                print_to_file(f"learnt_term_by[{transcribed_key},{arbit_role_name}.agent,t{time_indx}] => {{\n")
                start_block()
                write_msg_constraint(key_term,f"({msg_var_name}).encryptionKey",arbit_role_name,role_sig_name,time_indx)
                plaintxt_terms = msg_obj.msg_data[:-1]

                plaintxt_var_name = f"(({msg_var_name}).plaintext)"
                write_cat_constraint(Message(MsgType.CAT_TERM,plaintxt_terms),plaintxt_var_name,arbit_role_name,time_indx)
                end_block()
                print_to_file(f"}}\n")

            if  msg_obj.msg_type == MsgType.ATOM_TERM:
                var_name = msg_obj.msg_data.var_name
                print_to_file(f"{msg_var_name} = {arbit_role_name}.{role_sig_name}_{var_name}\n")
            elif msg_obj.msg_type == MsgType.CAT_TERM:
                write_cat_constraint(msg_obj,msg_var_name,arbit_role_name,time_indx)
            elif msg_obj.msg_type == MsgType.ENCRYPTED_TERM:
                write_enc_constraint(msg_obj,msg_var_name,arbit_role_name,time_indx)
            elif msg_obj.msg_type in [MsgType.LTK_TERM,MsgType.PUBK_TERM,MsgType.PRIVK_TERM]:
                transcribed_key = transcribe_key_term(msg_obj,arbit_role_name)
                print_to_file(f"{transcribed_key} = {msg_var_name}\n")

        for index,(_,msg_in_trace) in enumerate(msg_trace):
            ##unclear why separate case try to understand later
            ##maybe can change (enc ..) to (cat (enc ..)) so that it works automatically here
            if msg_in_trace.msg_type == MsgType.ENCRYPTED_TERM:
                enc_term_name = get_msg_var_name(msg_in_trace)
                ##if root term is an encrypted term then we will
                ##not have any other terms concatenated so only one term
                print_to_file(f"inds[t{index}.data] = 0\n")
                print_to_file(f"some {enc_term_name} : elems[t{index}.data] | {{\n")
                start_block()
                print_to_file(f"elems[t{index}.data] = {enc_term_name}\n")
                write_msg_constraint(msg_in_trace,enc_term_name,arbit_role_name,role_sig_name,index)
                end_block()
                print_to_file(f"}}\n")
            elif msg_in_trace.msg_type == MsgType.CAT_TERM:
                write_msg_constraint(msg_in_trace,f"t{index}.data",arbit_role_name,role_sig_name,index)
            else:
                write_msg_constraint(msg_in_trace,f"elems[t{index}.data]",arbit_role_name,role_sig_name,index)
    def transcribe_role_trace_to_pred(role_obj:Role,prot_name:str,role_sig_name:str):
        """the exec_pred_roleName created for each role, contains constraints for traces,
        timeslot the sender/receiver for all the timeslots"""
        def pred_header(pred_name:str):
            """adds predicate declaration starting block of code in which predicate
            is present"""
            print_to_file(f"// predicate follows below\n")
            print_to_file(f"pred {pred_name} {{\n")
            start_block()
        def pred_footer():
            """adds the end of predicate block"""
            end_block()
            print_to_file(f"}}\n")
            print_to_file(f"// end of predicate\n")
        def arbit_role_header(arbit_role_name):
            """adds the beginning block of quantification over all agents 
            of a particular role """
            print_to_file(f"all {arbit_role_name} : {role_sig_name} | {{\n")
            start_block()
        def arbit_role_footer():
            """adds the end of the block of code which quantifies over all 
            agents of a particular role"""
            end_block()
            print_to_file(f"}}\n")
        def timeslot_header(trace_len):
            """adds the quantification over all timeslots in the trace of
            the protocol"""
            print_to_file("some ")
            for i in range(trace_len-1):
                print_to_file(f"t{i},",add_space=False)
            print_to_file(f"t{trace_len-1} : Timeslot | {{\n",add_space=False)
            start_block()
        def timeslot_constraints(trace_len):
            """adds constraints for the timeslots in the existential qualification 
            to be in linear order"""
            for i in range(trace_len-1):
                print_to_file(f"t{i+1} in t{i}.(^next)\n")
        def only_sends_in_timelost_constraint(arbit_role_name,trace_len):
            """adds constraint so agent can only send/receive in the timeslots 
            mentioned in the protocol defintion"""
            print_to_file("t0 ")
            for i in range(1,trace_len):
                print_to_file(f"+ t{i} ",add_space=False)
            print_to_file(f" = sender.{arbit_role_name} + receiver.{arbit_role_name}\n",add_space=False)
        def send_recv_constraints(arbit_role_name,msg_trace:List[Tuple[SendRecv,Message]]):
            """adds constraints on the timeslot so that the appropiate agent is 
            sending/receiving messages"""
            for indx,(send_recv,_) in enumerate(msg_trace):
                if send_recv == SendRecv.SEND_TRACE:
                    print_to_file(f"t{indx}.sender = {arbit_role_name}\n")
                if send_recv == SendRecv.RECV_TRACE:
                    print_to_file(f"t{indx}.receiver = {arbit_role_name}\n")
        def timeslot_footer():
            """adds the end of the block performing existential quantification 
            over the timeslots"""
            end_block()
            print_to_file(f"}}\n")

        role_name = role_obj.role_name
        msg_trace = role_obj.msg_trace
        trace_len = len(msg_trace)
        arbit_role_name = f"arbitrary_{prot_name}_{role_name}"
        pred_name = f"exec_{prot_name}_{role_name}"
        pred_header(pred_name)
        arbit_role_header(arbit_role_name)
        timeslot_header(trace_len)

        timeslot_constraints(trace_len)
        print_to_file("\n")
        only_sends_in_timelost_constraint(arbit_role_name,trace_len)
        print_to_file("\n")
        send_recv_constraints(arbit_role_name,msg_trace)
        print_to_file("\n")

        transcribe_timeslot_msg(arbit_role_name,msg_trace,role_sig_name)

        timeslot_footer()
        arbit_role_footer()
        pred_footer()
    prot_name = prot_obj.prot_name
    for role in prot_obj.roles_arr:
        role_sig_name = f"{prot_name}_{role.role_name}"
        transcribe_role_vars_to_sig(role,role_sig_name)
        print_to_file("\n")
        transcribe_role_trace_to_pred(role,prot_name,role_sig_name)
        print_to_file("\n")

fresh_skelet_num = -1
def get_new_skelet_num():
    global fresh_skelet_num
    fresh_skelet_num += 1    
    return fresh_skelet_num
def transcribe_skelet(skelet_obj:Skeleton,file:io.TextIOWrapper):
    fresh_strand_num = -1
    space_lvl = 0
    def get_fresh_strand_num():
        nonlocal fresh_strand_num
        fresh_strand_num += 1
        return fresh_strand_num
    def print_to_file(txt:str,add_space = True):
        """helper function to print txt argument with correct level of indentation
        into generated file, add_space = True adds indentation, add_space = False
        does not"""
        if add_space:
            print(space_lvl*space_str,end="",file=file)
        print(txt,end="",file=file)
    def start_block():
        nonlocal space_lvl 
        space_lvl += 1
    def end_block():
        nonlocal space_lvl
        space_lvl -= 1
    def write_skel_sig(skel_obj:Skeleton,cur_skelet_num:int):
        def write_var_fields(skel_obj:Skeleton,cur_skelet_num:int):
            skel_obj.var_dict
            lst_var_names = list(skel_obj.var_dict.keys())
            for var_name in lst_var_names[:-1]:
                cur_var_obj = skel_obj.var_dict[var_name]
                print_to_file(f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}_{var_name}: one {vartype_to_str(cur_var_obj.var_type)},\n")
            var_name = lst_var_names[-1]
            cur_var_obj = skel_obj.var_dict[var_name]
            print_to_file(f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}_{var_name}: one {vartype_to_str(cur_var_obj.var_type)}\n")

        print_to_file(f"one sig skeleton_{skel_obj.prot_name}_{cur_skelet_num} {{\n")
        start_block()
        write_var_fields(skel_obj,cur_skelet_num)
        end_block()
        print_to_file(f"}}\n")
    def transcribe_strand(skel_obj:Skeleton,cur_strand:Strand,cur_skelet_num:int,cur_strand_num:int):
        skel_name = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}"
        strand_name = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}_strand{cur_strand_num}"
        strand_sig_name = f"{skel_obj.prot_name}_{cur_strand.role_name}"

        print_to_file(f"some {strand_name} : {skel_obj.prot_name}_{cur_strand.role_name} | {{\n")
        start_block()
        for skel_var_name,role_var_name in cur_strand.var_map.items():
            skel_var_name = f"{skel_name}_{skel_var_name}"
            role_var_name = f"{strand_sig_name}_{role_var_name}"
            print_to_file(f"{skel_name}.{skel_var_name} = {strand_name}.{role_var_name}\n")
        end_block()
        print_to_file(f"}}\n\n")
    def transcribe_constraints(skel_obj:Skeleton,cur_skelet_num:int):
        def not_in_attack_base(var_name:str):
            print_to_file(f"not ( {var_name} in baseKnown[Attacker]  )\n")
        def originates(strand_name:str,var_name:str):
            print_to_file(f"originates[{strand_name},{var_name}]\n")
        def generates(strand_name:str,var_name:str):
            print_to_file(f"generates[{strand_name},{var_name}]\n")
        def get_var_name_constr(skel_obj:Skeleton,cur_constr:Constraint,cur_skelet_num:int):
            cur_msg = cur_constr.msg_on_constr
            cur_type = cur_msg.msg_type
            if cur_type == MsgType.ATOM_TERM:
                cur_var = cur_msg.msg_data
                cur_var_name = cur_var.var_name
                sig_name     = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}"
                sig_var_name = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}_{cur_var_name}" 
                return f"{sig_name}.{sig_var_name}"
            elif cur_type == MsgType.LTK_TERM:
                name_1,name_2 = cur_msg.msg_data
                return f"getLTK[{name_1},{name_2}]"
            elif cur_type == MsgType.PRIVK_TERM:
                name_term = cur_msg.msg_data[0]
                name_var_term = name_term.msg_data
                cur_var_name = name_var_term.var_name

                sig_name     = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}"
                sig_var_name = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}_{cur_var_name}" 
                return f"getPRIVK[{sig_name}.{sig_var_name}]"
            elif cur_type == MsgType.PUBK_TERM:
                name_term = cur_msg.msg_data[0]
                name_var_term = name_term.msg_data
                cur_var_name = name_var_term.var_name

                sig_name     = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}"
                sig_var_name = f"skeleton_{skel_obj.prot_name}_{cur_skelet_num}_{cur_var_name}" 
                return f"getPUBK[{sig_name}.{sig_var_name}]"
        def transcr_non_orig(skel_obj:Skeleton,cur_constr:Constraint,cur_skelet_num:int):
            cur_constr_var_name = get_var_name_constr(skel_obj,cur_constr,cur_skelet_num)
            not_in_attack_base(cur_constr_var_name)
            strand_name = "aStrand"

            print_to_file(f"no {strand_name} : strand | {{\n")
            
            start_block()
            originates(strand_name,cur_constr_var_name)
            print_to_file("or\n")
            generates(strand_name,cur_constr_var_name)
            end_block()

            print_to_file(f"}}\n")
        def transcr_uniq_orig(skel_obj:Skeleton,cur_constr:Constraint,cur_skelet_num:int):
            cur_constr_var_name = get_var_name_constr(skel_obj,cur_constr,cur_skelet_num)
            not_in_attack_base(cur_constr_var_name)
            strand_name = "aStrand"

            print_to_file(f"one {strand_name} : strand | {{\n")

            start_block()
            originates(strand_name,cur_constr_var_name)
            print_to_file("or\n")
            generates(strand_name,cur_constr_var_name)
            end_block()

            print_to_file(f"}}\n")
        for cur_constr in skel_obj.orig_constr:
            if cur_constr.constr_type == ConstrType.NON_ORIG:
                transcr_non_orig(skel_obj,cur_constr,cur_skelet_num) 
            if cur_constr.constr_type == ConstrType.UNIQ_ORIG:
                transcr_uniq_orig(skel_obj,cur_constr,cur_skelet_num)
            print_to_file(f"\n")
    def write_constrain_pred(skel_obj:Skeleton,cur_skelet_num:int):
        print_to_file(f"pred constrain_skeleton_{skel_obj.prot_name}_{cur_skelet_num} {{\n") 
        start_block()
        for cur_strand in skel_obj.strand_list:
            cur_strand_num = get_fresh_strand_num()
            transcribe_strand(skel_obj,cur_strand,cur_skelet_num,cur_strand_num)
        transcribe_constraints(skel_obj,cur_skelet_num)
        end_block()
        print_to_file(f"}}\n")
    
    this_skel_num = get_fresh_strand_num()
    write_skel_sig(skelet_obj,cur_skelet_num=this_skel_num)
    write_constrain_pred(skelet_obj,cur_skelet_num=this_skel_num)
if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("cspa_file_path",help="Path to the cspa file to transcribe")
    parser.add_argument("run_file_path",help="Path to the forge file containing run constraints")
    parser.add_argument("out_file_path",help="Path where transcribed forge file will be saved")

    args = parser.parse_args()

    base_file_path = "./base_with_seq.frg"
    extra_func_path = "./extra_funcs.frg"

    prot_obj = None
    skel_obj = None
    with open(args.cspa_file_path) as f:
        s_expr = load_cspa_as_s_expr_new(f)
        print(f"Debug len s_expr is: {len(s_expr)}")
        tmp =  parse_file(s_expr)
        if type(tmp) == type([]):
            prot_obj,skel_obj = tmp 
        else:
            prot_obj = tmp
    with open(args.out_file_path,'w') as out_file:
        with open(base_file_path) as base_file:
            append_file(base_file,out_file)
        with open(extra_func_path) as extra_func_file:
            append_file(extra_func_file,out_file)
        transcribe_prot(prot_obj,out_file)
        if skel_obj is not None:
            transcribe_skelet(skel_obj,out_file)
        with open(args.run_file_path) as run_file:
            append_file(run_file,out_file)