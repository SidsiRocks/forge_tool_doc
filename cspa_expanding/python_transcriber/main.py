import argparse
import parser
import re
import io
import sexpdata

import new_transcribe
from pathlib import Path


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


def load_cspa_as_s_expr_new(file):
    """using get_root_s_expr_lst to parse multiple s-expr in one file"""
    result = []
    for _ in file:
        break
    str1 = file.read()
    lst = get_root_s_expr_lst(str1)
    for elm in lst:
        #print("processed element")
        #print(elm)
        #print("="*8)
        result.append(sexpdata.loads(elm))
    return result

#TODO: should strip lang and ipen has not been tested att all and might not be useful
# consider removing later
def re_match_full_str(re_expr:re.Pattern,txt:str):
    match_obj = re.match(re_expr,txt)
    return (match_obj is not None) and (match_obj.span()[1] == len(txt))

File = io.TextIOWrapper
def main(cpsa_file:File,destination_forge_file:File,base_file:File,extra_func_file:File,run_forge_file:File,should_strip_lang_and_open:bool,visualization_script_path:str|None):
    s_expr_lst = load_cspa_as_s_expr_new(cpsa_file)
    protocol = parser.parse_protocol(s_expr_lst[0])
    skeletons = [
        parser.parse_skeleton(s_expr, protocol) for s_expr in s_expr_lst[1:]
    ]
    transcribe_obj = new_transcribe.Transcribe_obj(destination_forge_file)
    transcribe_obj.import_file(base_file)
    transcribe_obj.import_file(extra_func_file)
    new_transcribe.transcribe_protocol(protocol, transcribe_obj)
    for skel_indx, skeleton in enumerate(skeletons):
        new_transcribe.transcribe_skeleton(skeleton, protocol,
                                           transcribe_obj, skel_indx)
    if should_strip_lang_and_open:
        # TODO add support for comments also here
        open_regex = re.compile(r"[\s]*open[\s]*\".*\"[\s]*\n")
        lang_forge_regex = re.compile(r"[\s]*#lang[\s]*forge[\s]*\n")
        option_regex = r"[\s]*option[\s]*run_sterling[\s]*\".*\"[\s]*\n"
        option_regex = re.compile(option_regex)
        for line in run_forge_file:
            if re_match_full_str(open_regex,line) or re_match_full_str(lang_forge_regex,line):
                continue
            if re_match_full_str(option_regex,line):
                transcribe_obj.print_to_file(f"option run_sterling \"{visualization_script_path}\"\n")
                continue
            transcribe_obj.print_to_file(line)
    else:
        transcribe_obj.import_file(run_forge_file)

def path_rel_to_script(path):
    script_path = Path(__file__).parent
    return (script_path / path).resolve()

#TODO: Currently have to run this file from the directory where it is located
# becuase of how path of base_with_seq.frg etc. is written can change to write
# this differently
if __name__ == "__main__":
    argument_parser = argparse.ArgumentParser(
        prog='CSPA to forge transcriber',
        description=
        'takes in CPSA code and converts it to appropiate forge predicates to model the protocol'
    )

    argument_parser.add_argument('cpsa_file_path')
    argument_parser.add_argument('run_forge_file_path')
    argument_parser.add_argument("--destination_forge_file_path")
    argument_parser.add_argument("--strip_lang_open_from_run_file",
                                 action='store_true')
    argument_parser.add_argument("--use_hash_base_file",action='store_true')
    argument_parser.add_argument("--visualization_script_path",type=str)

    args = argument_parser.parse_args()
    base_file_path = None
    if args.use_hash_base_file:
        base_file_path = path_rel_to_script("./base_with_seq_and_hash.frg")
    else:
        base_file_path = path_rel_to_script("./base_with_seq.frg")
    extra_func_path = path_rel_to_script( "./extra_funcs.frg" )
    cpsa_file_path = args.cpsa_file_path
    run_forge_file_path = args.run_forge_file_path
    destination_forge_file_name = args.destination_forge_file_path if args.destination_forge_file_path is not None else "protocol.frg"

    should_strip_lang_and_open = args.strip_lang_open_from_run_file
    visualization_script = args.visualization_script_path
    if should_strip_lang_and_open and visualization_script is None:
        raise RuntimeError(f"expected visualization script path if using strip file option should_strip_lang_and_open = {should_strip_lang_and_open} visualization_script = {visualization_script}")

    with open(cpsa_file_path) as cpsa_file:
        with open(destination_forge_file_name, 'w') as destination_forge_file:
            with open(base_file_path) as base_file:
                with open(extra_func_path) as extra_func_file:
                    with open(run_forge_file_path) as run_forge_file:
                        main(cpsa_file,destination_forge_file,base_file,extra_func_file,run_forge_file,should_strip_lang_and_open,visualization_script)
                        print(f"finish transcribing to {destination_forge_file_name}")
