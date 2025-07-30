import argparse
import parser
import re

import sexpdata

import new_transcribe


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
    args = argument_parser.parse_args()
    base_file_path = "./base_with_seq.frg"
    extra_func_path = "./extra_funcs.frg"
    cpsa_file_path = args.cpsa_file_path
    run_forge_file_path = args.run_forge_file_path
    destination_forge_file = args.destination_forge_file_path if args.destination_forge_file_path is not None else "protocol.frg"

    should_strip_lang_and_open = args.strip_lang_open_from_run_file

    with open(cpsa_file_path) as cpsa_file:
        s_expr_lst = load_cspa_as_s_expr_new(cpsa_file)
    #Assuming first s_expr is always a protocol and rest all are skeletons
    protocol = parser.parse_protocol(s_expr_lst[0])
    skeletons = [
        parser.parse_skeleton(s_expr, protocol) for s_expr in s_expr_lst[1:]
    ]
    with open(destination_forge_file, 'w') as forge_file:
        transcribe_obj = new_transcribe.Transcribe_obj(forge_file)
        with open(base_file_path) as base_file:
            transcribe_obj.import_file(base_file)
        with open(extra_func_path) as extra_func_file:
            transcribe_obj.import_file(extra_func_file)
        new_transcribe.transcribe_protocol(protocol, transcribe_obj)
        for skel_indx, skeleton in enumerate(skeletons):
            new_transcribe.transcribe_skeleton(skeleton, protocol,
                                               transcribe_obj, skel_indx)
        if should_strip_lang_and_open:
            with open(run_forge_file_path) as f:
                open_regex = re.compile(r"[\s]*open\".*\"[\s]*\n")
                lang_forge_regex = re.compile(r"[\s]*#lang[\s]*forge[\s]*\n")
                for line in f:
                    matches_open_regex = re.match(open_regex, line) is not None
                    matches_lang_regex = re.match(lang_forge_regex,
                                                  line) is not None
                    if matches_open_regex or matches_lang_regex:
                        continue
                    transcribe_obj.print_to_file(line)
        else:
            with open(run_forge_file_path) as run_forge_file:
                transcribe_obj.import_file(run_forge_file)
