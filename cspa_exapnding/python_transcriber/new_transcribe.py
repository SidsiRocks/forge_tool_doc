from os import process_cpu_count
from type_and_helpers import *
import io


class Transcribe_obj:

    def __init__(self, file: io.TextIOWrapper) -> None:
        self.space_lvl = 0
        self.fresh_num = 0
        self.space_str = " " * 2
        self.file = file

    def get_fresh_num(self):
        self.fresh_num += 1
        return self.fresh_num

    def start_block(self):
        self.space_lvl += 1

    def end_block(self):
        self.space_lvl -= 1

    def print_to_file(self, txt, add_space=True):
        if add_space:
            print(self.space_lvl * self.space_str, end="", file=self.file)
            print(txt, end="", file=self.file)

    def write_sig(self, sig_name: str, field_name_type: List[Tuple[str, str]]):
        self.print_to_file(f"sig {sig_name}{{")
        self.start_block()
        for field_name, field_type in field_name_type:
            self.print_to_file(f"{field_name} : {field_type}")
        self.end_block()
        self.print_to_file(f"}}")

    def start_predicate(self, pred_name: str):
        self.print_to_file(f"pred {pred_name} {{")
        self.start_block()

    def end_predicate(self):
        self.print_to_file(f"}}")

    def start_some_predicate(self, var_names: List[str], set_name: str):
        variables_str = ','.join(var_names)
        self.print_to_file(f"some {variables_str} : {set_name} | {{")

    def start_all_predicate(self, var_names: List[str], set_name: str):
        variables_str = ",".join(var_names)
        self.print_to_file(f"all {variables_str} : {set_name} | {{")

    def write_seq_data(self, seq_expr: str, seq_elms: List[str]):
        indices_strs = "+".join([str(i) for i in range(len(seq_elms))])
        self.print_to_file(f"inds[{seq_expr}] = {indices_strs}")
        for indx, elm in enumerate(seq_elms):
            self.print_to_file(f"{seq_expr}[{indx}] = {elm}")

    def create_role_context(self, role: Role, protocol: Protocol):
        role_sig_name = f"{protocol.protocol_name}_{role.role_name}"
        role_var_name = f"arbitrary_{role_sig_name}"
        return RoleTranscribeContext(role_sig_name, role_var_name, self, role)


@dataclass
class RoleTranscribeContext:
    role_sig_name: str
    role_var_name: str
    transcr: Transcribe_obj
    role: Role

    def get_variable_name(self, var_name: str):
        if var_name not in self.role.var_map:
            raise ParseException(
                f"cannot get var name for {var_name} not in {self.role.var_map}"
            )
        return f"{self.role_var_name}.{self.role_sig_name}_{var_name}"


def transcribe_role_to_sig(role: Role, role_sig_name: str,
                           transcr: Transcribe_obj):
    field_name_type = [(var_name, f"one {vartype_to_str(var.var_type)}")
                       for var_name, var in role.var_map.items()]
    transcr.write_sig(role_sig_name, field_name_type)


def transcribe_var(elm_expr: str, var: Variable,
                   role_context: RoleTranscribeContext):
    role_context.transcr.print_to_file(
        f"{elm_expr} = {role_context.get_variable_name(var.var_name)}")


def transcribe_enc(elm_expr: str, enc_term: EncTerm,
                   role_context: RoleTranscribeContext):
    #TODO: have to add semantics of when encrypted terms can be deciphered or not
    #one naive method would be only writing data and key constraints only when the
    #inverse key is known(this should only be when recieving the message though)
    #if sending the message only need to know the original key not inverse key
    transcr = role_context.transcr
    data_atom_names = [
        f"atom_{transcr.get_fresh_num()}" for _ in range(len(enc_term.data))
    ]
    data_expr = f"({elm_expr}).data"
    transcr.start_some_predicate(data_atom_names, f"elems[{data_expr}]")
    transcr.write_seq_data(data_expr, data_atom_names)
    for indx, data_atom_name in enumerate(data_atom_names):
        transcribe_non_cat(data_atom_name, enc_term.data[indx], role_context)
    key_expr = f"({elm_expr}).encryptionKey"
    match enc_term.key:
        case PubkTerm(_) as pubk:
            transcribe_pubk(key_expr, pubk, role_context)
        case PrivkTerm(_) as privk:
            transcribe_privk(key_expr, privk, role_context)
        case LtkTerm(_) as ltk:
            transcribe_ltk(key_expr, ltk, role_context)
    transcr.end_predicate()


def transcribe_ltk(elm_expr: str, ltk_term: LtkTerm,
                   role_context: RoleTranscribeContext):
    role_context.transcr.print_to_file(
        f"{elm_expr} = getLTK[{ltk_term.agent1_name},{ltk_term.agent2_name}]")


def transcribe_pubk(elm_expr: str, pubk_term: PubkTerm,
                    role_context: RoleTranscribeContext):
    role_context.transcr.print_to_file(
        f"{elm_expr} = getPUBK[{pubk_term.agent_name}]")


def transcribe_privk(elm_expr: str, privk_term: PrivkTerm,
                     role_context: RoleTranscribeContext):
    role_context.transcr.print_to_file(
        f"{elm_expr} = getPRIVK[{privk_term.agent_name}]")


def transcribe_non_cat(elm_expr: str, msg: NonCatTerm,
                       role_context: RoleTranscribeContext):
    match msg:
        case Variable(_, _) as var:
            transcribe_var(elm_expr, var, role_context)
        case LtkTerm(_, _) as ltk:
            transcribe_ltk(elm_expr, ltk, role_context)
        case PubkTerm(_) as pubk:
            transcribe_pubk(elm_expr, pubk, role_context)
        case PrivkTerm(_) as privk:
            transcribe_privk(elm_expr, privk, role_context)
        case EncTerm(_, _) as enc_term:
            transcribe_enc(elm_expr, enc_term, role_context)


def transcribe_indv_trace(role: Role, indx: int,
                          role_context: RoleTranscribeContext):
    send_recv, mesg = role.trace[indx]
    transcr = role_context.transcr
    role_var_name = role_context.role_var_name
    match send_recv:
        case SendRecv.SEND:
            transcr.print_to_file(f"t{indx}.sender = {role_var_name}")
        case SendRecv.RECV:
            transcr.print_to_file(f"t{indx}.receiver = {role_var_name}")
    match mesg:
        case CatTerm(_) as cat:
            sub_term_names = [f"sub_term_{i}" for i in range(len(cat.data))]
            transcr.write_seq_data(f"(t{indx}.data)", sub_term_names)
            for sub_term_name, sub_term in zip(sub_term_names, cat.data):
                transcribe_non_cat(sub_term_name, sub_term, role_context)
        case non_cat_mesg:
            atom_name = f"atom_{transcr.get_fresh_num()}"
            transcr.write_seq_data(f"(t{indx}.data)", [atom_name])
            transcribe_non_cat(atom_name, non_cat_mesg, role_context)


def transcribe_trace(role: Role, role_var_name: str,
                     role_context: RoleTranscribeContext):
    trace_len = len(role.trace)
    timeslot_names = [f"t{i}" for i in range(trace_len)]
    transcr = role_context.transcr
    transcr.start_some_predicate(timeslot_names, "Timeslot")
    for i in range(trace_len - 1):
        transcr.print_to_file(f"t{i+1} in t{i}.(^next)\n")
    all_timeslots_set = "+".join(timeslot_names)
    transcr.print_to_file(
        f"{all_timeslots_set} = sender.{role_var_name} + receiver.{role_var_name}\n"
    )
    for i, (_, _) in enumerate(role.trace):
        transcribe_indv_trace(role, i, role_context)
    transcr.end_predicate()


def transcribe_role(role: Role, role_context: RoleTranscribeContext):
    role_sig_name = role_context.role_sig_name
    transcr = role_context.transcr
    transcribe_role_to_sig(role, role_sig_name, transcr)
    transcr.start_predicate(f"exec_{role_sig_name}")
    transcr.start_all_predicate([f"arbitrary_{role_sig_name}"], role_sig_name)
    transcribe_trace(role, f"arbitrary_{role_sig_name}", role_context)
    transcr.end_predicate()
    transcr.end_predicate()


def transcribe_protocol(protocol: Protocol, transcr: Transcribe_obj):
    """Function to transcribe the protocol object returned by the parser
    contains nested functions to parse sub components like roles,signatures"""
    for role in protocol.role_arr:
        transcribe_role(role, transcr.create_role_context(role, protocol))
