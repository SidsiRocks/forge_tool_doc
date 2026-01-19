import xml.etree.ElementTree as ET
from dataclasses import dataclass
from typing import *
from type_and_helpers import *

SIG_STR = "sig"
FIELD_STR = "field"
TUPLE_STR = "tuple"
TYPES_STR = "types"

# each sig seems to only include atoms not present in its children when listing
# instances
@dataclass
class Field:
    name: str
    id: int
    parent_id: int
    tuples: List[List[str]]
    type_id: List[int]
    def __str__(self) -> str:
        return "\n".join([
            f"{self.name}"
            f"\tid:{self.id}",
            f"\tparent_id:{self.parent_id}",
            f"\ttuples:{sorted(self.tuples)}",
            f"\ttype_id:{self.type_id}"
        ])
    def __repr__(self) -> str:
        return self.__str__()

@dataclass
class Sig:
    name: str
    atoms: set[str]
    id: int
    parent_id: int
    is_builtin: bool
    def __str__(self) -> str:
        return "\n".join([
            f"{self.name}",
            f"\tatoms:{sorted(self.atoms)}",
            f"\tid:{self.id}",
            f"\tparent_id:{self.parent_id}",
            f"\tis_builtin:{self.is_builtin}"
        ])
    def __repr__(self) -> str:
        return self.__str__()

class Instance:
    sigs_name_map: Dict[str,Sig]
    sig_id_to_name: Dict[int,str]
    fields_name_map: Dict[str,Field]
    field_id_to_name: Dict[int,str]

    sig_to_parent_map: Dict[str,str]
    sig_to_child_map: Dict[str,List[str]]

    def __init__(self,sigs_name_map:Dict[str,Sig],sig_id_to_name:Dict[int,str],fields_name_map:Dict[str,Field],field_id_to_name:Dict[int,str]) -> None:
        self.sigs_name_map= sigs_name_map
        self.sig_id_to_name = sig_id_to_name
        self.fields_name_map = fields_name_map
        self.field_id_to_name = field_id_to_name

        self.sig_to_parent_map = {}
        for sig in self.sigs_name_map.values():
            if sig.parent_id != -1:
                parent_sig = self.sig_id_to_name[sig.parent_id]
                self.sig_to_parent_map[sig.name] = parent_sig
        self.sig_to_child_map = {}
        for child_sig,parent_sig in self.sig_to_parent_map.items():
            if parent_sig not in self.sig_to_child_map:
                self.sig_to_child_map[parent_sig] = []
            self.sig_to_child_map[parent_sig].append(child_sig)

    def all_sig_atoms(self,sig_name:str) -> Set[str]:
        children_atoms_set = set()
        for child in self.sig_to_child_map.get(sig_name,[]):
            cur_set = self.all_sig_atoms(child)
            children_atoms_set = children_atoms_set.union(cur_set)
        children_atoms_set = children_atoms_set.union(self.sigs_name_map[sig_name].atoms)
        return children_atoms_set

    def __str__(self) -> str:
        sig_strs = [str(sig) for sig in self.sigs_name_map.values()]
        field_strs = [str(field) for field in self.fields_name_map.values()]
        return "\n".join(sig_strs + field_strs)
    def __repr__(self) -> str:
        return self.__str__()



def parse_field(field_xml_obj:ET.Element):
    name = field_xml_obj.attrib["label"]
    id = int(field_xml_obj.attrib["ID"])
    parent_id = int(field_xml_obj.attrib["parentID"])
    xml_elm_children = list(field_xml_obj)

    tuples_as_elm = [element for element in xml_elm_children if element.tag == TUPLE_STR]
    types = [element for element in xml_elm_children if element.tag == TYPES_STR][0]
    type_ids = [int(type_.attrib["ID"]) for type_ in types]
    tuples_as_str = [[atom.attrib["label"] for atom in tuple_] for tuple_ in tuples_as_elm]

    return Field(name,id,parent_id,tuples_as_str,type_ids)

def parse_sig(sig:ET.Element):
    name = sig.attrib['label']
    atoms = set([atom.attrib['label'] for atom in sig])
    id = int(sig.attrib['ID'])
    parent_id = int(sig.attrib.get("parentID",-1))
    is_builtin = "builtin" in sig.attrib
    return Sig(name,atoms,id,parent_id,is_builtin)

def parse_instance(file_name:str):
    tree = ET.parse(file_name)
    root = tree.getroot()
    instance,_ = list(root)
    # forge_file_source = root[1].attrib["content"]

    sig_field_and_skolems = list(instance)
    sigs = [parse_sig(element) for element in sig_field_and_skolems if element.tag == SIG_STR]
    fields = [parse_field(element) for element in sig_field_and_skolems if element.tag == FIELD_STR]

    sigs_name_map = {sig.name:sig for sig in sigs}
    sig_id_to_name = {sig.id:sig.name for sig in sigs}
    fields_name_map = {field.name:field for field in fields}
    field_id_to_name = {field.id:field.name for field in fields}

    return Instance(sigs_name_map,sig_id_to_name,fields_name_map,field_id_to_name)

def binary_rel_to_dic(field:Field) -> Dict[str,str]:
    if len(field.type_id) != 2:
        raise RuntimeError("expected a binary relation here")
    return {tpl[0]:tpl[1] for tpl in field.tuples}

def get_timeslots(timeslot_sigs:Sig,next_rel:Field):
    next_rel_dic = binary_rel_to_dic(next_rel)
    first_timeslot = list(timeslot_sigs.atoms.difference(next_rel_dic.values()))[0]
    timeslots = [first_timeslot]
    while timeslots[-1] in next_rel_dic:
        timeslots.append(next_rel_dic[timeslots[-1]])
    return timeslots

@dataclass
class InstanceRelations:
    instance: Instance

    tuples: Set[str]
    ciphertexts: Set[str]
    hashed: Set[str]
    keys: Set[str]
    name: Set[str]
    text: Set[str]
    skey: Set[str]
    akey: Set[str]

    pubk_owners: Dict[str,str] # pubk -> name
    privk_owners: Dict[str,str] # privk -> name
    ltk_owners: Dict[str,Tuple[str,str]]


    sender_rel_dic: Dict[str,str]
    receiver_rel_dic: Dict[str,str]
    data_rel_dic: Dict[str,str]

    components_rel_dic: Dict[str,List[str]]
    plaintext_rel_dic: Dict[str,str]
    encryptionKey_rel_dic: Dict[str,str]
    hash_of_rel_dic: Dict[str,str]

    atom_to_message_map: Dict[str,Message]

def message_atom_to_key(message_atom:str,instance_relations:InstanceRelations) -> KeyTerm:
    if message_atom in instance_relations.pubk_owners:
        result = PubkTerm(instance_relations.pubk_owners[message_atom])
        instance_relations.atom_to_message_map[message_atom] = result
        return result
    elif message_atom in instance_relations.privk_owners:
        result = PrivkTerm(instance_relations.privk_owners[message_atom])
        instance_relations.atom_to_message_map[message_atom] = result
        return result
    elif message_atom in instance_relations.ltk_owners:
        owner1,owner2 = instance_relations.ltk_owners[message_atom]
        result = LtkTerm(owner1,owner2)
        instance_relations.atom_to_message_map[message_atom] = result
        return result
    else:
        var_type = MsgTypes.MESG
        if message_atom in instance_relations.skey:
            var_type = MsgTypes.SKEY
        elif message_atom in instance_relations.akey:
            var_type = MsgTypes.AKEY
        result = Variable(message_atom,var_type)
        instance_relations.atom_to_message_map[message_atom] = result
        return result

def message_atom_to_obj(message_atom:str,instance_relations:InstanceRelations) -> Message:
    if message_atom in instance_relations.atom_to_message_map:
        return instance_relations.atom_to_message_map[message_atom]
    if message_atom in instance_relations.tuples:
        msg_components = [message_atom_to_obj(msg_comp_atom,instance_relations) for msg_comp_atom in instance_relations.components_rel_dic[message_atom]]
        instance_relations.atom_to_message_map[message_atom] = CatTerm(msg_components)
    elif message_atom in instance_relations.ciphertexts:
        plaintext_of_msg = message_atom_to_obj(instance_relations.plaintext_rel_dic[message_atom],instance_relations)
        encryptionKey_of_msg = message_atom_to_key(instance_relations.encryptionKey_rel_dic[message_atom],instance_relations)
        instance_relations.atom_to_message_map[message_atom] = EncTermNoTpl(plaintext_of_msg,encryptionKey_of_msg)
    elif message_atom in instance_relations.hashed:
        hash_of_msg = message_atom_to_obj(instance_relations.hash_of_rel_dic[message_atom],instance_relations)
        instance_relations.atom_to_message_map[message_atom] = HashTerm(hash_of_msg)
    elif message_atom in instance_relations.keys:
        message_atom_to_key(message_atom,instance_relations)
    else:
        var_type = MsgTypes.MESG
        if message_atom in instance_relations.name:
            var_type = MsgTypes.NAME
        elif message_atom in instance_relations.text:
            var_type = MsgTypes.TEXT
        elif message_atom in instance_relations.skey:
            var_type = MsgTypes.SKEY
        elif message_atom in instance_relations.akey:
            var_type = MsgTypes.AKEY
        instance_relations.atom_to_message_map[message_atom] = Variable(message_atom,var_type)
    return instance_relations.atom_to_message_map[message_atom]

def transcribe_timeslot(timeslot:str,instance_relations:InstanceRelations):
    sender = instance_relations.sender_rel_dic[timeslot]
    receiver = instance_relations.receiver_rel_dic[timeslot]
    message_sent = message_atom_to_obj(instance_relations.data_rel_dic[timeslot],instance_relations)
    print(f"\\[ {escape_underscore(sender)}->{escape_underscore(receiver)}: {message_sent.latex_repr()} \\]")

def get_latex_visulaization(instance:Instance):
    timeslot_sigs = instance.sigs_name_map["Timeslot"]
    next_rel = instance.fields_name_map["next"]
    timeslots = get_timeslots(timeslot_sigs,next_rel)

    sender_rel_dic = binary_rel_to_dic(instance.fields_name_map["sender"])
    receiver_rel_dic = binary_rel_to_dic(instance.fields_name_map["receiver"])
    data_rel_dic = binary_rel_to_dic(instance.fields_name_map["data"])
    components_rel_dic: Dict[str,List[str]] = {}
    for tuple_atom,index,component in instance.fields_name_map["components"].tuples:
        index = int(index)
        if tuple_atom not in components_rel_dic:
            components_rel_dic[tuple_atom] = []
        for _ in range(index+1-len(components_rel_dic[tuple_atom])):
            components_rel_dic[tuple_atom].append("")
        components_rel_dic[tuple_atom][index] = component

    plaintext_rel_dic = binary_rel_to_dic(instance.fields_name_map["plaintext"])
    encryptionKey_rel_dic = binary_rel_to_dic(instance.fields_name_map["encryptionKey"])
    hash_of_rel_dic = binary_rel_to_dic(instance.fields_name_map["hash_of"])

    tuples = instance.all_sig_atoms("tuple")
    ciphertexts = instance.all_sig_atoms("Ciphertext")
    hashed = instance.all_sig_atoms("Hashed")
    keys = instance.all_sig_atoms("Key")
    name = instance.all_sig_atoms("name")
    text = instance.all_sig_atoms("text")
    skey = instance.all_sig_atoms("skey")
    akey = instance.all_sig_atoms("akey")

    privk_owners = {private_key:owner for _,private_key,owner in instance.fields_name_map["owners"].tuples}
    privk_pubk_pairs = {private_key:public_key for _,private_key,public_key in instance.fields_name_map["pairs"].tuples}
    pubk_owners = {privk_pubk_pairs[privk]:owner for privk,owner in privk_owners.items()}
    ltk_owners = {ltk_key:(owner1,owner2) for _,owner1,owner2,ltk_key in instance.fields_name_map["ltks"].tuples}

    instance_relations = InstanceRelations(instance=instance,tuples=tuples,
                                           ciphertexts=ciphertexts,hashed=hashed,
                                           keys=keys,name=name,text=text,
                                           skey=skey,akey=akey,
                                           pubk_owners=pubk_owners,
                                           privk_owners=privk_owners,
                                           ltk_owners=ltk_owners,
                                           sender_rel_dic=sender_rel_dic,
                                           receiver_rel_dic=receiver_rel_dic,
                                           data_rel_dic=data_rel_dic,
                                           components_rel_dic=components_rel_dic,
                                           plaintext_rel_dic=plaintext_rel_dic,
                                           encryptionKey_rel_dic=encryptionKey_rel_dic,
                                           hash_of_rel_dic=hash_of_rel_dic,
                                           atom_to_message_map={})

    header = """
\\documentclass{article}
\\usepackage{graphicx}
\\title{Instance Visualization}
\\author{Siddhartha Singh}
\\date{December 2025}
\\begin{document}
    """
    print(header)
    for timeslot in timeslots:
        transcribe_timeslot(timeslot,instance_relations)
    footer = """
\\end{document}
    """
    print(footer)

if __name__ == "__main__":
    get_latex_visulaization(parse_instance("test.xml"))
