import io
from abc import abstractmethod
from typing import List, Tuple, override
from enum import Enum

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
        self.print_to_file("}\n")

    def write_new_seq_constraint(self,seq_expr:str,seq_terms:List[NonCatTerm],send_recv:SendRecv,timeslot_expr:str,sig_context:"RoleTranscribeContext"):
        indices_str = "+".join([str(i) for i in range(len(seq_terms))])
        self.print_to_file(f"inds[{seq_expr}] = {indices_str}\n")

        seq_term_exprs : List[str]= []
        quantifier_variables : List[Tuple[int,str]] = []
        for indx,elm in enumerate(seq_terms):
            match elm:
                case EncTerm(_):
                    seq_term_expr = "enc_" + str(self.get_fresh_num())
                    seq_term_exprs.append(seq_term_expr)
                    quantifier_variables.append((indx,seq_term_expr))
                case _:
                    seq_term_expr = f"{seq_expr}[{indx}]"
                    seq_term_exprs.append(seq_term_expr)

        def transcribe_subterms():
            for indx,quantifier_variable in quantifier_variables:
                self.print_to_file(f"{seq_expr}[{indx}] = {quantifier_variable}\n")
            for indx,(seq_term_expr,seq_term) in enumerate(zip(seq_term_exprs,seq_terms)):
                transcribe_non_cat(seq_term_expr,seq_term,send_recv,timeslot_expr,sig_context)
        if len(quantifier_variables) != 0:
            with QuantifierPredicate(QuantiferEnum.SOME,[txt for indx,txt in quantifier_variables],f"elems[{seq_expr}]",self):
                transcribe_subterms()
        else:
            transcribe_subterms()
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
        skeleton_sig_name = f"skeleton_{skeleton.protocol_name}_{skel_num}"
        return SkeletonTranscribeContext(skeleton_sig_name=skeleton_sig_name,
                                         transcr=self,
                                         skeleton=skeleton,
                                         skel_num=skel_num)

class QuantiferEnum(Enum):
    SOME = 0
    ALL = 1
    ONE = 2
    NO = 3

    def __str__(self) -> str:
        enum_to_str = {
            QuantiferEnum.SOME: "some",
            QuantiferEnum.ALL: "all",
            QuantiferEnum.ONE: "one",
            QuantiferEnum.NO: "no"
        }
        return enum_to_str[self]

    def __repr__(self) -> str:
        return self.__str__()


@dataclass
class PredicateContext:
    pred_name: str
    transcr: Transcribe_obj

    def __enter__(self):
        self.transcr.print_to_file(f"pred {self.pred_name} {{\n")
        self.transcr.start_block()

    def __exit__(self, exc_type, exc_value, traceback):
        self.transcr.end_block()
        self.transcr.print_to_file(f"}}\n")


@dataclass
class QuantifierPredicate:
    quantifer_enum: QuantiferEnum
    var_names: List[str]
    set_name: str
    transcr: Transcribe_obj

    def __enter__(self):
        variables_str = ','.join(self.var_names)
        self.transcr.print_to_file(
            f"{self.quantifer_enum} {variables_str} : {self.set_name} | {{\n")
        self.transcr.start_block()

    def __exit__(self, exc_type, exc_value, traceback):
        self.transcr.end_block()
        self.transcr.print_to_file(f"}}\n")

@dataclass
class ImpliesPredicate:
    pre_condition:str
    transcr: Transcribe_obj
    def __enter__(self):
        self.transcr.print_to_file(f"{self.pre_condition} => {{\n")
        self.transcr.start_block()
    def __exit__(self,exc_type,exc_value,traceback):
        self.transcr.end_block()
        self.transcr.print_to_file(f"}}\n")

@dataclass
class SigContext:

    @abstractmethod
    def acess_variable(self, var_name: str) -> str:
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

    @abstractmethod
    def get_inv_key(self,key_term:KeyTerm) -> str:
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

    def get_agent(self):
        return f"{self.role_var_name}.agent"

    @override
    def get_inv_key(self, key_term: KeyTerm) -> str:
        match key_term:
            case LtkTerm(_):
                return self.get_base_term_str(key_term)
            case PubkTerm(_) as pubk:
                privk_term = PrivkTerm(pubk.agent_name)
                return self.get_base_term_str(privk_term)
            case PrivkTerm(_) as privk:
                pubk_term = PubkTerm(privk.agent_name)
                return self.get_base_term_str(pubk_term)
            case Variable(_) as var:
                if var.var_type not in [VarType.SKEY,VarType.AKEY]:
                    raise ParseException(f"For KeyTerm expected variableof vartype SKEY or AKEY not {var.var_type} of {var}")
                match var.var_type:
                    case VarType.SKEY:
                        return self.get_base_term_str(var)
                    case VarType.AKEY:
                        #TODO implement forge function to invert akey
                        raise ParseException("have to add invert key function in forge to implement this function")
                    case _:
                        raise ParseException(f"For KeyTerm expected variableof vartype SKEY or AKEY not {var.var_type} of {var}")

    # TODO maybe can use alias types for these things?
    def get_learnt_term_constraint(self,term_str:str,timeslot_str:str):
        role_agent_str = self.get_agent()
        return f"learnt_term_by[{term_str},{role_agent_str},{timeslot_str}]"

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
#TODO: cleaning up comments also

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

#TODO: can add comments to show what different parts of transcription correspond to
# perhaps
def transcribe_enc(elm_expr: str, enc_term: EncTerm,send_recv:SendRecv ,timeslot_expr:str,sig_context: RoleTranscribeContext):
    transcr = sig_context.get_transcr()
    data_atom_names = [
        f"atom_{transcr.get_fresh_num()}" for _ in range(len(enc_term.data))
    ]
    data_expr = f"({elm_expr}).plaintext"
    key_expr = f"({elm_expr}).encryptionKey"

    match send_recv:
        case SendRecv.SEND:
            pass
        case SendRecv.RECV:
            term_str = sig_context.get_inv_key(enc_term.key)
            transcr.print_to_file(f"learnt_term_by[{term_str},{sig_context.role_var_name}.agent,{timeslot_expr}]\n")
    transcr.write_new_seq_constraint(data_expr,enc_term.data,send_recv,timeslot_expr,sig_context)
    transcribe_base_term(key_expr,enc_term.key,send_recv,sig_context)

def transcribe_base_term(elm_expr:str,msg:BaseTerm,send_recv:SendRecv,role_context:SigContext):
    constraint_expr = f"{elm_expr} = {role_context.get_base_term_str(msg)}\n"
    role_context.get_transcr().print_to_file(constraint_expr)

def transcribe_non_cat(elm_expr: str, msg: NonCatTerm,send_recv:SendRecv,timeslot_expr:str,
                       role_context: RoleTranscribeContext):
    match msg:
        case EncTerm(_, _) as enc_term:
            transcribe_enc(elm_expr, enc_term,send_recv,timeslot_expr, role_context)
        case base_term:
            transcribe_base_term(elm_expr,msg,send_recv,role_context)

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
            transcr.write_new_seq_constraint(f"(t{indx}.data)",cat.data,send_recv,f"t{indx}",role_context)

        case non_cat_mesg:
            atom_name = f"atom_{transcr.get_fresh_num()}"
            transcr.write_new_seq_constraint(f"(t{indx}.data)",[non_cat_mesg],send_recv,f"t{indx}",role_context)


def transcribe_trace(role: Role, role_context: RoleTranscribeContext):
    trace_len = len(role.trace)
    timeslot_names = [f"t{i}" for i in range(trace_len)]
    transcr = role_context.transcr

    # Below code is writing nested predicates which impose constraints on
    # Timeslot, original code had a common some predicate instead with next
    # predicate within
    # Ex:
    # Original                   New
    # some t0,t1: Timeslot {     some t0: Timeslot{
    #   t1 in t0.(^next)           some t1: t0.(^next){
    # }                            }
    #                            }
    # the old code in ootway_rees example seemed to be slowing down the code
    # too much
    cur_set = "Timeslot"
    for timeslot_name in timeslot_names:
        transcr.print_to_file(f"some {timeslot_name} : {cur_set} {{\n")
        transcr.start_block()
        cur_set = f"{timeslot_name}.(^next)"

    all_timeslots_set = "+".join(timeslot_names)
    role_var_name = role_context.role_var_name
    transcr.print_to_file(f"{all_timeslots_set} = sender.{role_var_name} + receiver.{role_var_name}\n")
    for i in range(len(role.trace)):
        transcribe_indv_trace(role,i,role_context)
        role_context.get_transcr().print_to_file("\n")

    for _ in timeslot_names:
        transcr.end_block()
        transcr.print_to_file(f"}}\n")

def transcribe_role(role: Role, role_context: RoleTranscribeContext):
    role_sig_name = role_context.role_sig_name
    transcr = role_context.transcr
    transcribe_role_to_sig(role, role_sig_name, transcr)
    with PredicateContext(transcr=transcr, pred_name=f"exec_{role_sig_name}"):
        with QuantifierPredicate(QuantiferEnum.ALL,
                                 [role_context.role_var_name], role_sig_name,
                                 transcr):
            transcribe_trace(role, role_context)


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


def transcribe_strand(strand: Strand,
                      skeleton_transcr_context: SkeletonTranscribeContext,
                      role_transcr_context: RoleTranscribeContext):
    transcr = skeleton_transcr_context.transcr
    with QuantifierPredicate(QuantiferEnum.SOME,
                             [role_transcr_context.role_var_name],
                             role_transcr_context.role_sig_name, transcr):
        for skeleton_var_name, strand_var in strand.skeleton_to_strand_var_map.items(
        ):
            strand_var_str = role_transcr_context.acess_variable(
                strand_var.var_name)
            skeleton_var_str = skeleton_transcr_context.acess_variable(
                skeleton_var_name)
            transcr.print_to_file(f"{strand_var_str} = {skeleton_var_str}\n")


#TODO: Can simplifly functions related to transcribing publick key privk and others since they are very small
def transcribe_non_orig(non_orig: NonOrig,
                        skeleton_transcr_context: SkeletonTranscribeContext):
    transcr = skeleton_transcr_context.transcr
    for base_term in non_orig.terms:
        base_term_str = skeleton_transcr_context.get_base_term_str(base_term)
        with QuantifierPredicate(QuantiferEnum.NO, ["aStrand"], "strand",
                                 transcr):
            transcr.print_to_file(
                f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
            )


def transcribe_uniq_orig(uniq_orig: UniqOrig,
                         skeleton_transcr_context: SkeletonTranscribeContext):
    transcr = skeleton_transcr_context.transcr
    for base_term in uniq_orig.terms:
        base_term_str = skeleton_transcr_context.get_base_term_str(base_term)
        with QuantifierPredicate(QuantiferEnum.ONE, ["aStrand"], "strand",
                                 transcr):
            transcr.print_to_file(
                f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
            )


def transcribe_skeleton_to_predicate(skeleton: Skeleton, skel_num: int,
                                     skeleton_pred_name: str,
                                     transcr: Transcribe_obj,
                                     protocol: Protocol):
    with PredicateContext(skeleton_pred_name, transcr):
        skel_transcr_context = transcr.create_skeleton_context(
            skeleton, skel_num)
        strand_num = 0
        for constranint in skeleton.constraints_list:
            match constranint:
                case Strand(_) as strand:
                    role = protocol.role_obj_of_name(strand.role_name)
                    if role is None:
                        raise ParseException(f"there is a problem here")
                    role_context = transcr.create_role_context(
                        role, protocol,
                        transcr.role_var_name_in_skel_pred(
                            strand.role_name, skel_num, strand_num))
                    transcribe_strand(strand, skel_transcr_context,
                                      role_context)
                    strand_num += 1
                case NonOrig(_) as non_orig:
                    transcribe_non_orig(non_orig, skel_transcr_context)
                case UniqOrig(_) as uniq_org:
                    transcribe_uniq_orig(uniq_org, skel_transcr_context)


def transcribe_skeleton(skeleton: Skeleton, protocol: Protocol,
                        transcr: Transcribe_obj, skel_num: int):
    skeleton_sig_name = f"skeleton_{skeleton.protocol_name}_{skel_num}"
    skeleton_pred_name = f"constrain_skeleton_{skeleton.protocol_name}_{skel_num}"
    transcribe_skeleton_to_sig(skeleton, skeleton_sig_name, transcr)
    transcribe_skeleton_to_predicate(skeleton, skel_num, skeleton_pred_name,
                                     transcr, protocol)
