import xml.etree.ElementTree as ET
from dataclasses import dataclass
from typing import *

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
    def alt_repr(self) -> str:
        return "\n".join([
            f"\tname:{self.name}",
            f"\tid:{self.id}",
            f"\tparent_id:{self.parent_id}",
            f"\ttuples:{self.tuples}",
            f"\ttype_id:{self.type_id}"
        ])

@dataclass
class Sig:
    name: str
    atoms: List[str]
    id: int
    parent_id: int
    is_builtin: bool
    def alt_repr(self) -> str:
        return "\n".join([
            f"\tname:{self.name}",
            f"\tatoms:{self.atoms}",
            f"\tid:{self.id}",
            f"\tparent_id:{self.parent_id}",
            f"\tis_builtin:{self.is_builtin}"
        ])

@dataclass
class Instance:
    sigs_name_map: Dict[str,Sig]
    sig_id_to_name: Dict[int,str]

    fields_name_map: Dict[str,Field]
    field_id_to_name: Dict[int,str]

    forge_file_source: str
    def __str__(self) -> str:
        sig_strs = [f"{sig_name}\n"+sig.alt_repr() for sig_name,sig in self.sigs_name_map.items()]
        field_strs = [f"{field_name}\n"+field.alt_repr() for field_name,field in self.fields_name_map.items()]
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
    atoms = [atom.attrib['label'] for atom in sig]
    id = int(sig.attrib['ID'])
    parent_id = int(sig.attrib.get("parentID",-1))
    is_builtin = "builtin" in sig.attrib
    return Sig(name,atoms,id,parent_id,is_builtin)

def parse_instance():
    tree = ET.parse("test.xml")
    root = tree.getroot()
    instance,source = list(root)
    forge_file_source = source.attrib["content"]

    sig_field_and_skolems = list(instance)
    sigs = [parse_sig(element) for element in sig_field_and_skolems if element.tag == SIG_STR]
    fields = [parse_field(element) for element in sig_field_and_skolems if element.tag == FIELD_STR]

    sigs_name_map = {sig.name:sig for sig in sigs}
    sig_id_to_name = {sig.id:sig.name for sig in sigs}
    fields_name_map = {field.name:field for field in fields}
    field_id_to_name = {field.id:field.name for field in fields}

    return Instance(sigs_name_map,sig_id_to_name,fields_name_map,field_id_to_name,forge_file_source)
