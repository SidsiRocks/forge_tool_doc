from reader import *
from typing import *
import io
space_str = " "*4

ENC_MSG_STR = "enc"
CAT_MSG_STR = "cat"
ATOM_MSG_STR= "atom"
LTK_MSG_STR = "ltk"
PUBK_MSG_STR= "pubk"

def msg_type_to_str(msg_type:MsgType):
    msg_type_to_str_dict = {
        MsgType.ATOM_TERM : ATOM_MSG_STR,
        MsgType.ENCRYPTED_TERM: ENC_MSG_STR,
        MsgType.CAT_TERM: CAT_MSG_STR,
        MsgType.LTK_TERM: LTK_MSG_STR,
        MsgType.PUBK_TERM: PUBK_MSG_STR
    }
    return msg_type_to_str_dict[msg_type]

def append_file(org_file:io.TextIOWrapper,new_file:io.TextIOWrapper):
    for line in org_file:
        new_file.write(line)
def transcribe_prot(prot_obj:Protocol,file:io.TextIOWrapper):
    space_lvl = 0
    msg_num_avl = 0 
    def get_msg_num():
        nonlocal msg_num_avl
        msg_num_avl += 1
        return msg_num_avl
    def print_to_file(txt:str,add_space = True):
        if add_space:
            print(space_lvl*space_str,end="",file=file)
        print(txt,end="",file=file)
    def transcribe_role_vars_to_sig(role_obj:Role,role_sig_name:str):
        nonlocal space_lvl
        print_to_file(f"sig {role_sig_name} extends strand{{\n")
        space_lvl += 1
        item_lst = list(role_obj.var_dict.items())
        for var_name,var in item_lst[:-1]:
            print_to_file(f"{role_sig_name}_{var_name}: one {vartype_to_str(var.var_type)},\n")
        var_name,var = item_lst[-1]
        print_to_file(f"{role_sig_name}_{var_name}: one {vartype_to_str(var.var_type)}\n")
        space_lvl -= 1
        print_to_file(f"}}\n")
    def transcribe_timeslot_msg(arbit_role_name:str,msg_trace:List[Tuple[SendRecv,Message]],role_sig_name:str):
        def get_msg_var_name(msg_obj:Message):
            cur_num = str(get_msg_num())
            return msg_type_to_str(msg_obj.msg_type)+cur_num
        def write_msg_constraint(msg_obj:Message,msg_var_name:str,arbit_role_name:str,role_sig_name:str):
            def write_cat_constraint(msg_obj:Message,msg_var_name:str,arbit_role_name:str):
                def write_sub_term_header(msg_var_name,cat_sub_terms_names:List[str]):
                    nonlocal space_lvl
                    print_to_file(f"some ")
                    #we are only writing some instead of some disjoint which 
                    #means if two subterms have same shape and same data then 
                    #only one occurence being present may count as two being present
                    for sub_term_name in cat_sub_terms_names[:-1]:
                        print_to_file(f"{sub_term_name},",add_space=False)
                    print_to_file(f"{cat_sub_terms_names[-1]} : {msg_var_name} {{\n",add_space=False)
                    space_lvl += 1
                def write_sub_term_footer():
                    nonlocal space_lvl
                    space_lvl -= 1
                    print_to_file(f"}}\n")
                def write_data_constraint(msg_var_name:str,cat_sub_terms_names:List[str]):
                    print_to_file(f"{msg_var_name} = ")
                    print_to_file(f"{cat_sub_terms_names[0]} ",add_space=False)
                    for sub_term_name in cat_sub_terms_names[1:]:
                        print_to_file(f"+ {sub_term_name} ",add_space=False)
                    print_to_file("\n")
                cat_sub_terms_names = [get_msg_var_name(msg_sub_term) for msg_sub_term in msg_obj.msg_data]
                write_sub_term_header(msg_var_name,cat_sub_terms_names)
                write_data_constraint(msg_var_name,cat_sub_terms_names)
                for sub_term_name,sub_term_obj in zip(cat_sub_terms_names,msg_obj.msg_data):
                    write_msg_constraint(sub_term_obj,sub_term_name,arbit_role_name,role_sig_name)
                write_sub_term_footer()
            def write_enc_constraint(msg_obj:Message,msg_var_name:str,arbit_role_name:str):
                def write_enc_header():
                    get_msg_var_name(msg_obj)
                def write_enc_footer():
                    pass
                nonlocal space_lvl
                key_term = msg_obj.msg_data[-1]                
                write_msg_constraint(key_term,f"({msg_var_name}).encryptionKey",arbit_role_name,role_sig_name)
                plaintxt_terms = msg_obj.msg_data[:-1]

                plaintxt_var_name = f"(({msg_var_name}).plaintext)"
                if len(plaintxt_terms) == 1:
                    write_msg_constraint(plaintxt_terms[0],plaintxt_var_name,arbit_role_name,role_sig_name)
                else:
                    write_cat_constraint(Message(MsgType.CAT_TERM,plaintxt_terms),plaintxt_var_name,arbit_role_name)

            if  msg_obj.msg_type == MsgType.ATOM_TERM:
                var_name = msg_obj.msg_data.var_name
                print_to_file(f"{msg_var_name} = {arbit_role_name}.{role_sig_name}_{var_name}\n")
            elif msg_obj.msg_type == MsgType.CAT_TERM:
                write_cat_constraint(msg_obj,msg_var_name,arbit_role_name)
            elif msg_obj.msg_type == MsgType.ENCRYPTED_TERM:
                write_enc_constraint(msg_obj,msg_var_name,arbit_role_name)
            elif msg_obj.msg_type == MsgType.LTK_TERM:
                name_var_1,name_var_2 = msg_obj.msg_data
                print_to_file(f"getLTK[{name_var_1.msg_data.var_name},{name_var_2.msg_data.var_name}] = {msg_var_name}\n")
            elif msg_obj.msg_type == MsgType.PUBK_TERM:
                name_var = msg_obj.msg_data[0].msg_data                
                #print_to_file(f"((Keypairs.owners).({arbit_role_name}.{role_sig_name}_{name_var.var_name})).(KeyPairs.pairs) = {msg_var_name}\n")
                print_to_file(f"getPUBK[{arbit_role_name}.{role_sig_name}_{name_var.var_name}] = {msg_var_name}\n")
        nonlocal space_lvl
        for index,(_,msg_in_trace) in enumerate(msg_trace):
            if msg_in_trace.msg_type == MsgType.ENCRYPTED_TERM:
                enc_term_name = get_msg_var_name(msg_in_trace)
                print_to_file(f"some {enc_term_name} : t{index}.data | {{\n")
                space_lvl += 1
                print_to_file(f"t{index}.data = {enc_term_name}\n")
                write_msg_constraint(msg_in_trace,enc_term_name,arbit_role_name,role_sig_name)
                space_lvl -= 1
                print_to_file(f"}}\n")
            else:
                write_msg_constraint(msg_in_trace,f"t{index}.data",arbit_role_name,role_sig_name)
    def transcribe_role_trace_to_pred(role_obj:Role,prot_name:str,role_sig_name:str):
        def pred_header(pred_name:str):
            nonlocal space_lvl
            print_to_file(f"// predicate follows below\n")
            print_to_file(f"pred {pred_name} {{\n")
            space_lvl += 1
        def pred_footer():
            nonlocal space_lvl
            space_lvl -= 1
            print_to_file(f"}}\n")
            print_to_file(f"// end of predicate\n")
        def arbit_role_header(arbit_role_name):
            nonlocal space_lvl
            print_to_file(f"all {arbit_role_name} : {role_sig_name} | {{\n")
            space_lvl += 1
        def arbit_role_footer():
            nonlocal space_lvl
            space_lvl -= 1
            print_to_file(f"}}\n")
        def timeslot_header(trace_len):
            nonlocal space_lvl
            print_to_file("some ")
            for i in range(trace_len-1):
                print_to_file(f"t{i},",add_space=False)
            print_to_file(f"t{trace_len-1} : Timeslot | {{\n",add_space=False)
            space_lvl += 1
        def timeslot_constraints(trace_len):
            for i in range(trace_len-1):
                print_to_file(f"t{i} in t{i+1}.(^next)\n")
        def only_sends_in_timelost_constraint(arbit_role_name,trace_len):
            print_to_file("t0 ")
            for i in range(1,trace_len):
                print_to_file(f"+ t{i} ",add_space=False)
            print_to_file(f" = sender.{arbit_role_name} + receiver.{arbit_role_name}\n",add_space=False)
        def send_recv_constraints(arbit_role_name,msg_trace:List[Tuple[SendRecv,Message]]):
            for indx,(send_recv,_) in enumerate(msg_trace):
                if send_recv == SendRecv.SEND_TRACE:
                    print_to_file(f"t{indx}.sender = {arbit_role_name}\n")
                if send_recv == SendRecv.RECV_TRACE:
                    print_to_file(f"t{indx}.receiver = {arbit_role_name}\n")
        def timeslot_footer():
            nonlocal space_lvl
            space_lvl -= 1
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

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("cspa_file_path",help="Path to the cspa file to transcribe")
    parser.add_argument("run_file_path",help="Path to the forge file containing run constraints")
    parser.add_argument("out_file_path",help="Path where transcribed forge file will be saved")

    args = parser.parse_args()

    base_file_path = "./base.frg"
    extra_func_path = "./extra_funcs.frg"

    with open(args.cspa_file_path) as f:
        s_expr = load_cspa_as_s_expr(f)
        parse_prot =  parse_protocol(s_expr)
    with open(args.out_file_path,'w') as out_file:
        with open(base_file_path) as base_file:
            append_file(base_file,out_file)
        with open(extra_func_path) as extra_func_file:
            append_file(extra_func_file,out_file)
        transcribe_prot(parse_prot,out_file)
        with open(args.run_file_path) as run_file:
            append_file(run_file,out_file)