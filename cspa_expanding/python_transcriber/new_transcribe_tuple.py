from collections import defaultdict
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
        if txt == "\n":
            add_space = False
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

    # def write_new_seq_constraint(self,seq_expr:str,seq_terms:List[NonCatTerm],send_recv:SendRecv,timeslot_expr:str,sig_context:"RoleOrSkelTranscrContext"):
    #     indices_str = "+".join([str(i) for i in range(len(seq_terms))])
    #     self.print_to_file(f"inds[{seq_expr}] = {indices_str}\n")

    #     seq_term_exprs : List[str]= []
    #     quantifier_variables : List[Tuple[int,str]] = []
    #     for indx,elm in enumerate(seq_terms):
    #         match elm:
    #             case EncTerm(_):
    #                 seq_term_expr = "enc_" + str(self.get_fresh_num())
    #                 seq_term_exprs.append(seq_term_expr)
    #                 quantifier_variables.append((indx,seq_term_expr))
    #             case _:
    #                 seq_term_expr = f"{seq_expr}[{indx}]"
    #                 seq_term_exprs.append(seq_term_expr)

    #     def transcribe_subterms():
    #         for indx,quantifier_variable in quantifier_variables:
    #             self.print_to_file(f"{seq_expr}[{indx}] = {quantifier_variable}\n")
    #         for indx,(seq_term_expr,seq_term) in enumerate(zip(seq_term_exprs,seq_terms)):
    #             transcribe_non_cat(seq_term_expr,seq_term,send_recv,timeslot_expr,sig_context)
    #     if len(quantifier_variables) != 0:
    #         # with QuantifierPredicate(QuantiferEnum.SOME,[txt for indx,txt in quantifier_variables],f"elems[{seq_expr}]",self):
    #         #     transcribe_subterms()
    #         enc_var_names = [seq_term_expr for _,seq_term_expr in quantifier_variables]
    #         enc_expressions = [f"({seq_expr})[{indx}]" for indx,_ in quantifier_variables]
    #         with LetClauseContext(enc_var_names,enc_expressions,self):
    #             transcribe_subterms()
    #     else:
    #         transcribe_subterms()

    def get_name_for_msg_term(self,non_cat_term:NonCatTerm) -> str:
        """returns a name for a message term, to be used for let clauses and
        existential quantification"""
        fresh_num = str(self.get_fresh_num())
        match non_cat_term:
            case EncTerm(_):
                return "enc_" + fresh_num
            case EncTermNoTpl(_):
                return "enc_" + fresh_num
            case SeqTerm(_):
                return "seq_" + fresh_num
            case HashTerm(_):
                return "hash_"+ fresh_num
            case LtkTerm(_):
                return "ltk_" + fresh_num
            case PubkTerm(_):
                return "pubk_"+fresh_num
            case PrivkTerm(_):
                return "privk_"+fresh_num
            case Variable(_) as var:
                match var.var_type:
                    case MsgTypes.NAME:
                        return "name_"+fresh_num
                    case MsgTypes.TEXT:
                        return "text_"+fresh_num
                    case MsgTypes.SKEY:
                        return "skey_"+fresh_num
                    case MsgTypes.AKEY:
                        return "akey_"+fresh_num
                    case MsgTypes.MESG:
                        return "mesg_"+fresh_num

    def write_new_seq_constraint(self,seq_expr:str,seq_terms:List[NonCatTerm],send_recv:SendRecv,timeslot_expr:str,sig_context:"RoleOrSkelTranscrContext"):
        seq_component_names = [self.get_name_for_msg_term(seq_component) for seq_component in seq_terms]
        seq_component_exprs = [f"({seq_expr})[{indx}]" for indx in range(len(seq_terms))]

        indices_str = "+".join([str(i) for i in range(len(seq_terms))])
        self.print_to_file(f"inds[{seq_expr}] = {indices_str}\n")
        with LetClauseContext(seq_component_names,seq_component_exprs,self):
            all_seq_components = " + ".join([f"{indx}->{comp_name}" for indx,comp_name in enumerate(seq_component_names)])
            self.print_to_file(f"{seq_expr} = {all_seq_components}\n")
            for comp_name,comp_term in zip(seq_component_names,seq_terms):
                transcribe_non_cat(comp_name,comp_term,send_recv,timeslot_expr,sig_context)

    def role_var_name_in_prot_pred(self, role_name, prot_name):
        return f"arbitrary_{role_name}_{prot_name}"

    def role_var_name_in_skel_pred(self, role_name: str, skel_num: int,
                                   strand_num: int):
        return f"skeleton_{role_name}_{skel_num}_strand_{strand_num}"

    def create_role_context(self, role: Role, protocol: Protocol,
                            role_var_name: str):
        role_sig_name = get_role_sig_name(role,protocol)
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
class LetClauseContext:
    var_name: List[str]
    var_expression: List[str]
    transcr: Transcribe_obj

    def __enter__(self):
        if len(self.var_name) != len(self.var_expression):
            raise ParseException("For let clause should have equal number of variable names and expressions")
        for var_name,var_expression in zip(self.var_name,self.var_expression):
            self.transcr.print_to_file(f"let {var_name}  = {var_expression} | {{\n")
        self.transcr.start_block()

    def __exit__(self,exc_type,exc_value,traceback):
        num_blocks = len(self.var_name)
        close_str = "}" * num_blocks
        self.transcr.end_block()
        self.transcr.print_to_file(close_str + "\n")

@dataclass
class InstanceContext:
    instance_name:str
    transcr:Transcribe_obj
    def __enter__(self):
        self.transcr.print_to_file(f"inst {self.instance_name} {{\n")
        self.transcr.start_block()
    def __exit__(self,exc_type,exc_value,traceback):
        self.transcr.end_block()
        self.transcr.print_to_file(f"}}\n")
@dataclass
class TimeslotContext:
    timeslot_names: List[str]
    transcr:Transcribe_obj
    nested_indent:bool

    def __enter__(self):
        cur_set = "Timeslot"
        for timeslot_name in self.timeslot_names:
            self.transcr.print_to_file(f"some {timeslot_name} : {cur_set} {{\n")
            if self.nested_indent:
                self.transcr.start_block()
            cur_set = f"{timeslot_name}.(^next)"
        if not self.nested_indent:
            self.transcr.start_block()

    def __exit__(self,exc_type,exc_value,traceback):
        if self.nested_indent:
            for _ in self.timeslot_names:
                self.transcr.end_block()
                self.transcr.print_to_file(f"}}\n")
        else:
            self.transcr.end_block()
            self.transcr.print_to_file("}"*len(self.timeslot_names)+"\n")
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

    def get_strand_var(self):
        return self.role_var_name

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
                if var.var_type not in [MsgTypes.SKEY,MsgTypes.AKEY]:
                    raise ParseException(f"For KeyTerm expected variableof vartype SKEY or AKEY not {var.var_type} of {var}")
                match var.var_type:
                    case MsgTypes.SKEY:
                        return self.get_base_term_str(var)
                    case MsgTypes.AKEY:
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
        if var_name in predefined_constants:
            return var_name
        return f"{self.skeleton_sig_name}.{self.get_skeleton_var_name(var_name)}"

    def get_skeleton_var_name(self, var_name: str):
        if var_name not in self.skeleton.non_strand_vars_map and var_name not in self.skeleton.strand_vars_map:
            raise ParseException(
                F"cannot acess variable with name {var_name} not in {self.skeleton.non_strand_vars_map} and {self.skeleton.strand_vars_map}"
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

RoleOrSkelTranscrContext = RoleTranscribeContext | SkeletonTranscribeContext

def transcribe_role_to_sig(role: Role, role_sig_name: str,
                           transcr: Transcribe_obj):
    field_name_type = [(f"{role_sig_name}_{var_name}",
                        f"one {vartype_to_str(var.var_type)}")
                       for var_name, var in role.var_map.items()]
    parent_sig_name = "strand"
    transcr.write_sig(role_sig_name, parent_sig_name, field_name_type, None)

#TODO: can add comments to show what different parts of transcription correspond to
# perhaps
def transcribe_enc(elm_expr: str, enc_term: EncTerm,send_recv:SendRecv ,timeslot_expr:str,sig_context: RoleOrSkelTranscrContext):
    transcr = sig_context.get_transcr()
    data_atom_names = [
        f"atom_{transcr.get_fresh_num()}" for _ in range(len(enc_term.data))
    ]
    data_expr = f"({elm_expr}).plaintext.components"
    key_expr = f"({elm_expr}).encryptionKey"

    match send_recv:
        case SendRecv.SEND:
            pass
        case SendRecv.RECV:
            term_str = sig_context.get_inv_key(enc_term.key)
            match sig_context:
                case RoleTranscribeContext(_):
                    transcr.print_to_file(f"learnt_term_by[{term_str},{sig_context.role_var_name}.agent,{timeslot_expr}]\n")
                case SkeletonTranscribeContext(_):
                    pass
    transcr.write_new_seq_constraint(data_expr,enc_term.data,send_recv,timeslot_expr,sig_context)
    transcribe_base_term(key_expr,enc_term.key,send_recv,sig_context)

def transcribe_enc_no_tpl(elm_expr:str,enc_no_tpl:EncTermNoTpl,send_recv:SendRecv,timeslot_expr:str,sig_context:RoleOrSkelTranscrContext):
    transcr = sig_context.get_transcr()
    match send_recv:
        case SendRecv.SEND:
            pass
        case SendRecv.RECV:
            term_str = sig_context.get_inv_key(enc_no_tpl.key)
            match sig_context:
                case RoleTranscribeContext(_):
                    transcr.print_to_file(f"learnt_term_by[{term_str},{sig_context.role_var_name}.agent,{timeslot_expr}]\n")
                case SkeletonTranscribeContext(_):
                    pass
    data_expr = f"({elm_expr}).plaintext"
    key_expr = f"({elm_expr}).encryptionKey"
    transcribe_base_term(data_expr,enc_no_tpl.data,send_recv,sig_context)
    transcribe_base_term(key_expr,enc_no_tpl.key,send_recv,sig_context)

def transcribe_hash(elm_expr: str,hash_term:HashTerm,send_recv:SendRecv,timeslot_expr:str,sig_context:RoleOrSkelTranscrContext):
    transcr = sig_context.get_transcr()
    transcr.print_to_file(f"{elm_expr} in Hashed\n")
    hash_of_expr = f"({elm_expr}).hash_of"
    transcribe_non_cat(hash_of_expr,hash_term.hash_of,send_recv,timeslot_expr,sig_context)

def transcribe_base_term(elm_expr:str,msg:BaseTerm,send_recv:SendRecv,role_context:SigContext):
    constraint_expr = f"{elm_expr} = {role_context.get_base_term_str(msg)}\n"
    role_context.get_transcr().print_to_file(constraint_expr)

def transcribe_non_cat(elm_expr: str, msg: NonCatTerm,send_recv:SendRecv,timeslot_expr:str,
                       role_context: RoleOrSkelTranscrContext):
    match msg:
        case EncTerm(_, _) as enc_term:
            transcribe_enc(elm_expr, enc_term,send_recv,timeslot_expr, role_context)
        case EncTermNoTpl(_,_) as enc_no_tpl_term:
            transcribe_enc_no_tpl(elm_expr,enc_no_tpl_term,send_recv,timeslot_expr,role_context)
        case HashTerm(_) as hash_term:
            transcribe_hash(elm_expr,hash_term,send_recv,timeslot_expr,role_context)
        case SeqTerm(_):
            raise ParseException(f"not handling SeqTerm in this transcriber")
        case base_term:
            transcribe_base_term(elm_expr,base_term,send_recv,role_context)

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
            transcr.write_new_seq_constraint(f"(t{indx}.data.components)",cat.data,send_recv,f"t{indx}",role_context)

        case non_cat_mesg:
            #atom_name = f"atom_{transcr.get_fresh_num()}"
            #transcr.write_new_seq_constraint(f"(t{indx}.data.components)",[non_cat_mesg],send_recv,f"t{indx}",role_context)
            transcribe_non_cat(f"(t{indx}.data)",non_cat_mesg,send_recv,f"t{indx}",role_context)

def transcribe_freshly_gen_constr(role:Role,role_context:RoleTranscribeContext):
    freshly_gen_constrs:List[FreshlyGenConstraint] = []
    for role_contstr in role.role_constraints:
        match role_contstr:
            case FreshlyGenConstraint(_) as fresh_gen_constr:
                freshly_gen_constrs.append(fresh_gen_constr)

    var_first_occur : Dict[int,List[Variable]] = defaultdict(list)

    for fresh_gen_constr in freshly_gen_constrs:
        for variable in fresh_gen_constr.terms:
            first_occur = var_first_occur_in_trace(role.trace,variable)
            match first_occur:
                case None:
                    raise ParseException(f"cannot impose freshly generated constraint if not present in trace")
                case indx,send_recv,msg_term:
                    if send_recv == SendRecv.RECV:
                        raise ParseException(f"cannot impose freshly generated constraint if get variable as recieving")
                    var_first_occur[indx].append(variable)

    for indx,variables in var_first_occur.items():
        freshly_gen_tuples = " + ".join([f"({role_context.acess_variable(var.var_name)})->t{indx}" for var in variables])
        role_context.transcr.print_to_file(f"({freshly_gen_tuples}) in ({role_context.get_agent()}).generated_times\n")

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
    # cur_set = "Timeslot"
    # for timeslot_name in timeslot_names:
    #     transcr.print_to_file(f"some {timeslot_name} : {cur_set} {{\n")
    #     transcr.start_block()
    #     cur_set = f"{timeslot_name}.(^next)"

    with TimeslotContext(timeslot_names,transcr,False):
        transcribe_freshly_gen_constr(role,role_context)
        all_timeslots_set = "+".join(timeslot_names)
        role_var_name = role_context.role_var_name
        transcr.print_to_file(f"{all_timeslots_set} = sender.{role_var_name} + receiver.{role_var_name}\n")
        for i in range(len(role.trace)):
            transcribe_indv_trace(role,i,role_context)
            role_context.get_transcr().print_to_file("\n")

    # for _ in timeslot_names:
    #     transcr.end_block()
    #     transcr.print_to_file(f"}}\n")
def transcribe_most_role_constr(role:Role,role_context:RoleTranscribeContext):
    role_constratins = role.role_constraints
    for constraint in role_constratins:
        match constraint:
            case NonOrig(_) as non_orig:
                transcribe_non_orig(non_orig,role_context)
            case UniqOrig(_) as uniq_orig:
                transcribe_uniq_orig(uniq_orig,role_context)
            case NotEqConstraint(_) as not_eq:
                transcribe_not_eq(not_eq,role_context)
            case FreshlyGenConstraint(_):
                #this case has to be present inside the code where
                #existential quantification over timeslots takes place
                pass

def transcribe_role(role: Role, role_context: RoleTranscribeContext):
    role_sig_name = role_context.role_sig_name
    transcr = role_context.transcr
    transcribe_role_to_sig(role, role_sig_name, transcr)

    with PredicateContext(transcr=transcr, pred_name=f"exec_{role_sig_name}"):
        with QuantifierPredicate(QuantiferEnum.ALL,
                                 [role_context.role_var_name], role_sig_name,
                                 transcr):
            transcribe_most_role_constr(role,role_context)
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


def transcribe_skeleton_to_sig(skeleton: Skeleton,protocol:Protocol, skeleton_sig_name: str,
                               transcr: Transcribe_obj):
    non_strand_field_name_type = [
        (f"{skeleton_sig_name}_{var_name}",
         f"one {vartype_to_str(var.var_type)}")
        for var_name, var in skeleton.non_strand_vars_map.items()
    ]
    strand_field_name_types = [
        (f"{skeleton_sig_name}_{var_name}",
         f"one {rolesig_of_role_obj_type(protocol,role_obj_type)}")
        for var_name,role_obj_type in skeleton.strand_vars_map.items()
    ]
    all_field_name_types = non_strand_field_name_type + strand_field_name_types
    transcr.write_sig(skeleton_sig_name, None, all_field_name_types, "one")


def transcribe_strand(strand: Strand,
                      skeleton_transcr_context: SkeletonTranscribeContext,
                      role_transcr_context: RoleTranscribeContext):
    transcr = skeleton_transcr_context.transcr
    # TODO: assumes some predicate here so if there are multiple strands all of the same role this would match with only one of them, this may not always be desirable look into this later
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
                        skeleton_transcr_context: RoleOrSkelTranscrContext):
    transcr = skeleton_transcr_context.transcr
    for base_term in non_orig.terms:
        base_term_str = skeleton_transcr_context.get_base_term_str(base_term)
        with QuantifierPredicate(QuantiferEnum.NO, ["aStrand"], "strand",
                                 transcr):
            transcr.print_to_file(
                f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
            )

def transcribe_uniq_orig(uniq_orig: UniqOrig,
                         skeleton_transcr_context: RoleOrSkelTranscrContext):
    transcr = skeleton_transcr_context.transcr
    for base_term in uniq_orig.terms:
        base_term_str = skeleton_transcr_context.get_base_term_str(base_term)
        match skeleton_transcr_context:
            case SkeletonTranscribeContext(_):
                with QuantifierPredicate(QuantiferEnum.ONE, ["aStrand"], "strand",
                                         transcr):
                    transcr.print_to_file(
                        f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
                    )
            case RoleTranscribeContext(_) as role_transcr:
                #TODO: modify uniq-orig to only take in terms that can be generated
                strand_name = role_transcr.get_agent()
                transcr.print_to_file(f"(generated_times.Timeslot).({base_term_str}) = {strand_name}\n")
                # with QuantifierPredicate(QuantiferEnum.ONE, ["aStrand"], "strand",
                #                          transcr):
                #     transcr.print_to_file(
                #         f"originates[aStrand,{base_term_str}] or generates [aStrand,{base_term_str}]\n"
                #     )

def transcribe_not_eq(not_eq:NotEqConstraint,
                      skeleton_transcr_context:RoleOrSkelTranscrContext):
    transcr = skeleton_transcr_context.transcr
    term1_str = skeleton_transcr_context.get_base_term_str(not_eq.term1)
    term2_str = skeleton_transcr_context.get_base_term_str(not_eq.term2)
    transcr.print_to_file(f"{term1_str} != {term2_str}\n")

def transcribe_indv_trace_constraint(skeleton:Skeleton,indv_trace_constraint:IndvSendRecvInConstraint,timeslot_name:str,transcr:Transcribe_obj,skel_transcr_context:SkeletonTranscribeContext):
    send_recv = indv_trace_constraint.trace_type
    send_recv_strand = indv_trace_constraint.sender_reciever_strand
    message = indv_trace_constraint.message
    match send_recv:
        case SendRecv.SEND:
            transcr.print_to_file(f"{timeslot_name}.sender = {skel_transcr_context.acess_variable(send_recv_strand)}\n")
        case SendRecv.RECV:
            transcr.print_to_file(f"{timeslot_name}.receiver = {skel_transcr_context.acess_variable(send_recv_strand)}\n")
    data_in_timeslot = None
    match message:
        case CatTerm(data):
            transcr.write_new_seq_constraint(f"({timeslot_name}.data.components)",data,send_recv,f"{timeslot_name}",skel_transcr_context)
        case _ as non_cat_term:
            transcribe_non_cat(f"({timeslot_name}.data)",non_cat_term,
                                     send_recv,timeslot_name,skel_transcr_context)
def transcribe_trace_constraint(trace_constraint:TraceConstraint,
                                skeleton:Skeleton,skel_num:int,
                                skeleton_pred_name:str,transcr:Transcribe_obj,
                                protocol:Protocol,
                                skel_transcr_context:SkeletonTranscribeContext):
    trace_name = trace_constraint.trace_name
    trace_pred_name = f"{skeleton_pred_name}_{trace_name}"
    indv_trace_constraints = trace_constraint.trace_elms
    trace_len = len(indv_trace_constraints)

    timeslot_names = [f"t_{i}" for i in range(trace_len)]
    with PredicateContext(trace_pred_name,transcr):
        with TimeslotContext(timeslot_names,transcr,False):
            for timeslot_name,indv_trace_constraint in zip(timeslot_names,indv_trace_constraints):
                transcribe_indv_trace_constraint(skeleton,indv_trace_constraint,
                                                 timeslot_name,transcr,skel_transcr_context)
                transcr.print_to_file("\n")

    return trace_pred_name
def transcribe_skeleton_to_predicate(skeleton: Skeleton, skel_num: int,
                                     skeleton_pred_name: str,
                                     transcr: Transcribe_obj,
                                     protocol: Protocol,
                                     skel_transcr_context:SkeletonTranscribeContext):
    non_trace_constraints : List[Strand | NonOrig | UniqOrig | NotEqConstraint] = []
    trace_constraints : List[TraceConstraint] = []
    for constraint in skeleton.constraints_list:
        match constraint:
            case TraceConstraint(_) as trace:
                trace_constraints.append(trace)
            case _:
                non_trace_constraints.append(constraint)

    trace_pred_names = []
    for trace_constraint in trace_constraints:
        cur_trace_pred_name = transcribe_trace_constraint(trace_constraint,skeleton,
                                                          skel_num,skeleton_pred_name,
                                                          transcr,protocol,skel_transcr_context)
        trace_pred_names.append(cur_trace_pred_name)

    with PredicateContext(skeleton_pred_name, transcr):
        strand_num = 0
        for constranint in non_trace_constraints:
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
                case NotEqConstraint(_) as not_eq:
                    transcribe_not_eq(not_eq,skel_transcr_context)

        for trace_pred_name in trace_pred_names:
            transcr.print_to_file(trace_pred_name + "\n")


def transcribe_skeleton(skeleton: Skeleton, protocol: Protocol,
                        transcr: Transcribe_obj, skel_num: int):
    skeleton_sig_name = f"skeleton_{skeleton.protocol_name}_{skel_num}"
    skeleton_pred_name = f"constrain_skeleton_{skeleton.protocol_name}_{skel_num}"
    skel_transcr_context = transcr.create_skeleton_context(skeleton,skel_num)

    transcribe_skeleton_to_sig(skeleton,protocol, skeleton_sig_name, transcr)
    transcribe_skeleton_to_predicate(skeleton, skel_num, skeleton_pred_name,
                                     transcr, protocol,skel_transcr_context)
def write_bound_expressions(cur_node:str,instance_bound:AltInstanceBounds,transcr:Transcribe_obj):
    instance_counts = instance_bound.sig_counts
    if cur_node in alt_subtypes:
        cur_node_subs = alt_subtypes[cur_node]
        for subtype in cur_node_subs:
            write_bound_expressions(subtype,instance_bound,transcr)
        non_zero_count_subtype = list(filter(lambda sub: (instance_counts[sub] != 0),cur_node_subs))
        if cur_node in subtypes_are_exhaustive:
            subtype_sigs = " + ".join(non_zero_count_subtype)
            transcr.print_to_file(f"{cur_node} = {subtype_sigs}\n")
        else:
            child_sigs = non_zero_count_subtype
            total_child_elms = sum([instance_counts[child] for child in child_sigs])
            extra_no_elms = instance_counts[cur_node] - total_child_elms
            extra_elms = [f"`{cur_node}{indx}" for indx in range(extra_no_elms)]
            total_elms = " + ".join(extra_elms + child_sigs)
            transcr.print_to_file(f"{cur_node} = {total_elms}\n")
    else:
        cur_count = instance_counts[cur_node]
        if cur_count != 0:
            sig_elements = " + ".join([f"`{cur_node}{indx}" for indx in range(instance_counts[cur_node])])
            transcr.print_to_file(f"{cur_node} = {sig_elements}\n")

def transcribe_instance(instance_bound:AltInstanceBounds,prot:Protocol,transcr:Transcribe_obj):
    with InstanceContext(instance_bound.instance_name,transcr):
        write_bound_expressions(MESG_SIG,instance_bound,transcr)
        transcr.print_to_file("\n")
        write_bound_expressions(TIMESLOT_SIG,instance_bound,transcr)
        transcr.print_to_file("\n")

        sig_counts = instance_bound.sig_counts
        #write depth bound for plaintext
        #set values for pairs and owners relation
        possible_seq_len = "+".join([str(i) for i in range(instance_bound.tuple_length)])
        #transcr.print_to_file(f"plaintext in {CIPHER_SIG} -> ({possible_seq_len}) -> {MESG_SIG}\n")
        #transcr.print_to_file("\n")

        #no nested tuples
        transcr.print_to_file(f"components in tuple -> ({possible_seq_len}) -> (Key + name + text + Ciphertext + tuple)\n")
        microtick_bound = instance_bound.encryption_depth + 1
        microtick_instances = " + ".join([f"`{MICROTICK_SIG}{i}" for i in range(microtick_bound)])
        transcr.print_to_file(f"{MICROTICK_SIG} = {microtick_instances}\n")

        transcr.print_to_file(f"KeyPairs = `KeyPairs0\n")
        pubk_count,privk_count,name_count = sig_counts[PUBK_SIG],sig_counts[PRIVK_SIG],sig_counts[NAME_SIG]
        if pubk_count != privk_count or pubk_count != name_count or privk_count != name_count:
            raise ParseException(f"pubk,privk and name bounds are {pubk_count},{privk_count},{name_count} are not all equal currently only supporting instances where they are all equal")

        #keypairs pairs tuples
        pubk_privk_tpls = " + ".join([f"`{PRIVK_SIG}{i}->`{PUBK_SIG}{i}" for i in range(pubk_count)])
        transcr.print_to_file(f"pairs = KeyPairs -> ({pubk_privk_tpls})\n")

        key_owner_tpls = " + ".join([f"`{PRIVK_SIG}{i}->`name{i}" for i in range(name_count-1)] + [f"`{PRIVK_SIG}{name_count-1}->`Attacker0"])
        transcr.print_to_file(f"owners = KeyPairs -> ({key_owner_tpls})\n")
        transcr.print_to_file(f"no ltks\n")
        transcr.print_to_file("\n")
        #next relation on Timeslot
        num_timeslots = sig_counts[TIMESLOT_SIG]
        time_next_tpls = " + ".join([f"`{TIMESLOT_SIG}{indx}->`{TIMESLOT_SIG}{indx+1}" for indx in range(num_timeslots-1)])
        transcr.print_to_file(f"next = {time_next_tpls}\n")
        #mt_next relation on microticks
        microtick_next_tpls = " + ".join([f"`{MICROTICK_SIG}{indx} -> `{MICROTICK_SIG}{indx+1}" for indx in range(microtick_bound - 1)])
        transcr.print_to_file(f"mt_next = {microtick_next_tpls}\n")

        transcr.print_to_file("\n")
        role_sig_names = {role.role_name: get_role_sig_name(role,prot) for role in prot.role_arr}
        for role_name,role_sig_name in role_sig_names.items():
            cur_count = instance_bound.role_counts[role_name]
            cur_role_elms = " + ".join([f"`{role_sig_name}{i}" for i in range(cur_count)])
            transcr.print_to_file(f"{role_sig_name} = {cur_role_elms}\n")
        transcr.print_to_file(f"AttackerStrand = `AttackerStrand0\n")
        all_strands = " + ".join(list(role_sig_names.values()) + [ "AttackerStrand" ])
        transcr.print_to_file(f"strand = {all_strands}\n")

