import io
from abc import abstractmethod
from typing import override

from type_and_helpers import *


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

    def import_file(self, other_forge_file: io.TextIOWrapper):
        for line in other_forge_file:
            self.print_to_file(line)

#TODO: can change signature modifier to use an enum instead of a plain string
# like below

    def write_sig(self, sig_name: str, parent_sig_name: None | str,
                  field_name_type: List[Tuple[str,
                                              str]], sig_modifier: str | None):
        parent_sig_name = "" if parent_sig_name is None else f"extends {parent_sig_name} "
        sig_modifier = "" if sig_modifier is None else sig_modifier + " "
        self.print_to_file(
            f"{sig_modifier}sig {sig_name} {parent_sig_name}{{\n")
        self.start_block()
        for field_name, field_type in field_name_type[:-1]:
            self.print_to_file(f"{field_name} : {field_type},\n")
        field_name, field_type = field_name_type[-1]
        self.print_to_file(f"{field_name} : {field_type}\n")

        self.end_block()
        self.print_to_file(f"}}\n")

    def start_predicate(self, pred_name: str):
        self.print_to_file(f"pred {pred_name} {{\n")
        self.start_block()

    def end_predicate(self):
        self.end_block()
        self.print_to_file(f"}}\n")

    def start_some_predicate(self, var_names: List[str], set_name: str):
        variables_str = ','.join(var_names)
        self.print_to_file(f"some {variables_str} : {set_name} | {{\n")
        self.start_block()

    def start_all_predicate(self, var_names: List[str], set_name: str):
        variables_str = ",".join(var_names)
        self.print_to_file(f"all {variables_str} : {set_name} | {{\n")
        self.start_block()

    def start_one_predicate(self, var_names: List[str], set_name: str):
        variables_str = ",".join(var_names)
        self.print_to_file(f"all {variables_str} : {set_name} | {{\n")
        self.start_block()

    def start_no_predicate(self, var_names: List[str], set_name: str):
        variables_str = ",".join(var_names)
        self.print_to_file(f"no {variables_str} : {set_name} | {{\n")
        self.start_block()


#TODO: would be very helpful to write using context operations,
# i.e with as

    def write_seq_data(self, seq_expr: str, seq_elms: List[str]):
        indices_strs = "+".join([str(i) for i in range(len(seq_elms))])
        self.print_to_file(f"inds[{seq_expr}] = {indices_strs}\n")
        self.start_some_predicate(seq_elms, f"elems[{seq_expr}]")
        for indx, elm in enumerate(seq_elms):
            self.print_to_file(f"{seq_expr}[{indx}] = {elm}\n")

    def role_var_name_in_prot_pred(self, role_name, prot_name):
        return f"arbitrary_{role_name}_{prot_name}"

    def role_var_name_in_skel_pred(self, role_name: str, skel_num: int,
                                   strand_num: int):
        return f"skeleton_{role_name}_{skel_num}_strand_{strand_num}"

    def create_role_context(self, role: Role, protocol: Protocol,
                            role_var_name: str):
        role_sig_name = f"{protocol.protocol_name}_{role.role_name}"
        return RoleTranscribeContext(role_sig_name, role_var_name, self, role)

    def create_skeleton_context(self, skeleton: Skeleton, skel_num: int):
        skelton_sig_name = f"skelton_{skeleton.protocol_name}_{skel_num}"
        return SkeletonTranscribeContext(skeleton_sig_name=skelton_sig_name,
                                         transcr=self,
                                         skeleton=skeleton,
                                         skel_num=skel_num)


@dataclass
class SigContext:

    @abstractmethod
    def acess_variable(self, var_name: str) -> str:
        pass

    @abstractmethod
    def get_role_var_name(self, var_name: str) -> str:
        pass

    @abstractmethod
    def get_transcr(self) -> Transcribe_obj:
        pass

    @abstractmethod
    def get_ltk_str(self, ltk_term: LtkTerm) -> str:
        pass

    @abstractmethod
    def get_pubk_str(self, pubk_term: PubkTerm) -> str:
        pass

    @abstractmethod
    def get_privk_str(self, privk_term: PrivkTerm) -> str:
        pass

    @abstractmethod
    def get_base_term_str(self, base_term: BaseTerm) -> str:
        pass


#TODO: come up with better variable name than role_var_name
@dataclass
class RoleTranscribeContext(SigContext):
    role_sig_name: str
    role_var_name: str
    transcr: Transcribe_obj
    role: Role

    @override
    def acess_variable(self, var_name: str):
        if var_name not in self.role.var_map:
            raise ParseException(
                f"cannot get acess variable with name {var_name} not in {self.role.var_map}"
            )
        return f"{self.role_var_name}.{self.get_role_var_name(var_name)}"

    @override
    def get_role_var_name(self, var_name: str):
        if var_name not in self.role.var_map:
            raise ParseException(
                f"cannot get var name for {var_name} not in {self.role.var_map}"
            )
        return f"{self.role_sig_name}_{var_name}"

    @override
    def get_transcr(self) -> Transcribe_obj:
        return self.transcr

    @override
    def get_ltk_str(self, ltk_term: LtkTerm) -> str:
        acess_agent_1_var = self.acess_variable(ltk_term.agent1_name)
        acess_agent_2_var = self.acess_variable(ltk_term.agent2_name)
        return f"getLTK[{acess_agent_1_var},{acess_agent_2_var}]"

    @override
    def get_pubk_str(self, pubk_term: PubkTerm) -> str:
        return f"getPUBK[{self.acess_variable(pubk_term.agent_name)}]"

    @override
    def get_privk_str(self, privk_term: PrivkTerm) -> str:
        return f"getPRIVK[{self.acess_variable(privk_term.agent_name)}]"

    @override
    def get_base_term_str(self, base_term: BaseTerm) -> str:
        match base_term:
            case LtkTerm(_) as ltk:
                return self.get_ltk_str(ltk)
            case PubkTerm(_) as pubk:
                return self.get_pubk_str(pubk)
            case PrivkTerm(_) as privk:
                return self.get_privk_str(privk)
            case Variable(_) as var:
                return self.acess_variable(var.var_name)


@dataclass
class SkeletonTranscribeContext(SigContext):
    skeleton_sig_name: str
    transcr: Transcribe_obj
    skeleton: Skeleton
    skel_num: int

    @override
    def acess_variable(self, var_name):
        if var_name not in self.skeleton.skeleton_vars_dict:
            raise ParseException(
                F"cannot acess variable with name {var_name} not in {self.skeleton.skeleton_vars_dict}"
            )
        return f"{self.skeleton_sig_name}.{self.get_skeleton_var_name(var_name)}"

    @override
    def get_skeleton_var_name(self, var_name: str):
        if var_name not in self.skeleton.skeleton_vars_dict:
            raise ParseException(
                F"cannot acess variable with name {var_name} not in {self.skeleton.skeleton_vars_dict}"
            )
        return f"{self.skeleton_sig_name}_{var_name}"

    @override
    def get_ltk_str(self, ltk_term: LtkTerm) -> str:
        acess_agent_1_var = self.acess_variable(ltk_term.agent1_name)
        acess_agent_2_var = self.acess_variable(ltk_term.agent2_name)
        return f"getLTK[{acess_agent_1_var},{acess_agent_2_var}]"

    @override
    def get_pubk_str(self, pubk_term: PubkTerm) -> str:
        return f"getPUBK[{self.acess_variable(pubk_term.agent_name)}]"

    @override
    def get_privk_str(self, privk_term: PrivkTerm) -> str:
        return f"getPRIVK[{self.acess_variable(privk_term.agent_name)}]"


#TODO: can remove some code duplication here

    @override
    def get_base_term_str(self, base_term: BaseTerm) -> str:
        match base_term:
            case LtkTerm(_) as ltk:
                return self.get_ltk_str(ltk)
            case PubkTerm(_) as pubk:
                return self.get_pubk_str(pubk)
            case PrivkTerm(_) as privk:
                return self.get_privk_str(privk)
            case Variable(_) as var:
                return self.acess_variable(var.var_name)

    @override
    def get_transcr(self) -> Transcribe_obj:
        return self.transcr


def transcribe_role_to_sig(role: Role, role_sig_name: str,
                           transcr: Transcribe_obj):
    field_name_type = [(f"{role_sig_name}_{var_name}",
                        f"one {vartype_to_str(var.var_type)}")
                       for var_name, var in role.var_map.items()]
    parent_sig_name = "strand"
    transcr.write_sig(role_sig_name, parent_sig_name, field_name_type, None)


def transcribe_var(elm_expr: str, var: Variable, sig_context: SigContext):
    sig_context.get_transcr().print_to_file(
        f"{elm_expr} = {sig_context.acess_variable(var.var_name)}\n")


#TODO: can add comments to show what different parts of transcription correspond to
# perhaps
def transcribe_enc(elm_expr: str, enc_term: EncTerm, sig_context: SigContext):
    #TODO: have to add semantics of when encrypted terms can be deciphered or not
    #one naive method would be only writing data and key constraints only when the
    #inverse key is known(this should only be when recieving the message though)
    #if sending the message only need to know the original key not inverse key
    transcr = sig_context.get_transcr()
    data_atom_names = [
        f"atom_{transcr.get_fresh_num()}" for _ in range(len(enc_term.data))
    ]
    data_expr = f"({elm_expr}).plaintext"
    transcr.start_some_predicate(data_atom_names, f"elems[{data_expr}]")
    transcr.write_seq_data(data_expr, data_atom_names)
    for data_atom_name, data_term in zip(data_atom_names, enc_term.data):
        transcribe_non_cat(data_atom_name, data_term, sig_context)
    transcr.end_predicate()
    #ending predicate started in write_seq_data (might not be correct position may have to change this)
    key_expr = f"({elm_expr}).encryptionKey"
    match enc_term.key:
        case PubkTerm(_) as pubk:
            transcribe_pubk(key_expr, pubk, sig_context)
        case PrivkTerm(_) as privk:
            transcribe_privk(key_expr, privk, sig_context)
        case LtkTerm(_) as ltk:
            transcribe_ltk(key_expr, ltk, sig_context)
    transcr.end_predicate()


def transcribe_ltk(elm_expr: str, ltk_term: LtkTerm, sig_context: SigContext):
    sig_context.get_transcr().print_to_file(
        f"{elm_expr} = {sig_context.get_ltk_str(ltk_term)}\n")


def transcribe_pubk(elm_expr: str, pubk_term: PubkTerm,
                    role_context: SigContext):
    role_context.get_transcr().print_to_file(
        f"{elm_expr} = {role_context.get_pubk_str(pubk_term)}\n")


def transcribe_privk(elm_expr: str, privk_term: PrivkTerm,
                     role_context: SigContext):
    role_context.get_transcr().print_to_file(
        f"{elm_expr} = {role_context.get_privk_str(privk_term)}\n")


def transcribe_non_cat(elm_expr: str, msg: NonCatTerm,
                       role_context: SigContext):
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
            transcr.print_to_file(f"t{indx}.sender = {role_var_name}\n")
        case SendRecv.RECV:
            transcr.print_to_file(f"t{indx}.receiver = {role_var_name}\n")
    match mesg:
        case CatTerm(_) as cat:
            sub_term_names = [f"sub_term_{i}" for i in range(len(cat.data))]
            transcr.write_seq_data(f"(t{indx}.data)", sub_term_names)
            for sub_term_name, sub_term in zip(sub_term_names, cat.data):
                transcribe_non_cat(sub_term_name, sub_term, role_context)
            transcr.end_predicate()
            #ending predicate started in write_seq_data (might not be correct position may have to change this)

        case non_cat_mesg:
            atom_name = f"atom_{transcr.get_fresh_num()}"
            transcr.write_seq_data(f"(t{indx}.data)", [atom_name])
            transcribe_non_cat(atom_name, non_cat_mesg, role_context)
            transcr.end_predicate()
            #ending predicate started in write_seq_data (might not be correct position may have to change this)


def transcribe_trace(role: Role, role_context: RoleTranscribeContext):
    trace_len = len(role.trace)
    timeslot_names = [f"t{i}" for i in range(trace_len)]
    transcr = role_context.transcr
    transcr.start_some_predicate(timeslot_names, "Timeslot")
    for i in range(trace_len - 1):
        transcr.print_to_file(f"t{i+1} in t{i}.(^next)\n")
    all_timeslots_set = "+".join(timeslot_names)
    role_var_name = role_context.role_var_name
    transcr.print_to_file(
        f"{all_timeslots_set} = sender.{role_var_name} + receiver.{role_var_name}\n"
    )
    for i, (_, _) in enumerate(role.trace):
        transcribe_indv_trace(role, i, role_context)
        role_context.get_transcr().print_to_file("\n")
    transcr.end_predicate()


def transcribe_role(role: Role, role_context: RoleTranscribeContext):
    role_sig_name = role_context.role_sig_name
    transcr = role_context.transcr
    transcribe_role_to_sig(role, role_sig_name, transcr)
    transcr.start_predicate(f"exec_{role_sig_name}")
    transcr.start_all_predicate([role_context.role_var_name], role_sig_name)
    transcribe_trace(role, role_context)
    transcr.end_predicate()
    transcr.end_predicate()


def transcribe_protocol(protocol: Protocol, transcr: Transcribe_obj):
    """Function to transcribe the protocol object returned by the parser
    contains nested functions to parse sub components like roles,signatures"""
    for role in protocol.role_arr:
        transcribe_role(
            role,
            transcr.create_role_context(
                role, protocol,
                transcr.role_var_name_in_prot_pred(role.role_name,
                                                   protocol.protocol_name)))


def transcribe_skeleton_to_sig(skeleton: Skeleton, skeleton_sig_name: str,
                               transcr: Transcribe_obj):
    field_name_type = [
        (f"{skeleton_sig_name}_{var_name}",
         f"one {vartype_to_str(var.var_type)}")
        for var_name, var in skeleton.skeleton_vars_dict.items()
    ]
    transcr.write_sig(skeleton_sig_name, None, field_name_type, "one")


#TODO: conisder using a context object for writing skeleton variable names as well
def transcribe_strand(strand: Strand,
                      skelton_transcr_context: SkeletonTranscribeContext,
                      role_transcr_context: RoleTranscribeContext):
    transcr = skelton_transcr_context.transcr
    transcr.start_some_predicate([role_transcr_context.role_var_name],
                                 role_transcr_context.role_sig_name)
    for skelton_var_name, strand_var in strand.skeleton_to_strand_var_map.items(
    ):
        strand_var_str = role_transcr_context.acess_variable(
            strand_var.var_name)
        skelton_var_str = skelton_transcr_context.acess_variable(
            skelton_var_name)
        transcr.print_to_file(f"{strand_var_str} = {skelton_var_str}\n")
    transcr.end_predicate()


#TODO: maybe using with for start and ending predicates so that the code is clearer
#TODO: can simplifly lots of similar functions like start_no_predicate,start_one_predicate etc. Can also simplifly functions related to transcribing publick key privk and others since they are very small
def transcribe_non_orig(non_orig: NonOrig,
                        skeleton_transcr_context: SkeletonTranscribeContext):
    transcr = skeleton_transcr_context.transcr
    for base_term in non_orig.terms:
        base_term_str = skeleton_transcr_context.get_base_term_str(base_term)
        transcr.start_no_predicate(["aStrand"], "strand")
        transcr.print_to_file(
            f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
        )
        transcr.end_predicate()


def transcribe_uniq_orig(uniq_orig: UniqOrig,
                         skeleton_transcr_context: SkeletonTranscribeContext):
    transcr = skeleton_transcr_context.transcr
    for base_term in uniq_orig.terms:
        base_term_str = skeleton_transcr_context.get_base_term_str(base_term)
        transcr.start_one_predicate(["aStrand"], "strand")
        transcr.print_to_file(
            f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
        )
        transcr.end_predicate()


def transcribe_skeleton_to_predicate(skeleton: Skeleton, skel_num: int,
                                     skeleton_pred_name: str,
                                     transcr: Transcribe_obj,
                                     protocol: Protocol):
    transcr.start_predicate(skeleton_pred_name)
    skel_transcr_context = transcr.create_skeleton_context(skeleton, skel_num)
    strand_num = 0
    for constranint in skeleton.constraints_list:
        match constranint:
            case Strand(_) as strand:
                role = protocol.role_obj_of_name(strand.role_name)
                if role is None:
                    raise ParseException(f"there is a problem here")
                role_context = transcr.create_role_context(
                    role, protocol,
                    transcr.role_var_name_in_skel_pred(strand.role_name,
                                                       skel_num, strand_num))
                transcribe_strand(strand, skel_transcr_context, role_context)
                strand_num += 1
            case NonOrig(_) as non_orig:
                transcribe_non_orig(non_orig, skel_transcr_context)
            case UniqOrig(_) as uniq_org:
                transcribe_uniq_orig(uniq_org, skel_transcr_context)
    transcr.end_predicate()


def transcribe_skeleton(skeleton: Skeleton, protocol: Protocol,
                        transcr: Transcribe_obj, skel_num: int):
    skeleton_sig_name = f"skeleton_{skeleton.protocol_name}_{skel_num}"
    skeleton_pred_name = f"constrain_skeleton_{skeleton.protocol_name}_{skel_num}"
    transcribe_skeleton_to_sig(skeleton, skeleton_sig_name, transcr)
    transcribe_skeleton_to_predicate(skeleton, skel_num, skeleton_pred_name,
                                     transcr, protocol)
