import sexpdata
import argparse
import parser
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


if __name__ == "__main__":
    argument_parser = argparse.ArgumentParser(
        prog='CSPA to forge transcriber',
        description=
        'takes in CPSA code and converts it to appropiate forge predicates to model the protocol'
    )
    argument_parser.add_argument('cpsa_file_path')
    argument_parser.add_argument("--forge_file_path")
    args = argument_parser.parse_args()
    base_file_path = "./base_with_seq.frg"
    extra_func_path = "./extra_funcs.frg"
    cpsa_file_path = args.cpsa_file_path
    forge_file_path = args.forge_file_path if args.forge_file_path is not None else "protocol.frg"

    s_expr_lst = load_cspa_as_s_expr_new(cpsa_file_path)
    #Assuming first s_expr is always a protocol and rest all are skeletons
    protocol = parser.parse_protocol(s_expr_lst[0])
    skeletons = [
        parser.parse_skeleton(s_expr, protocol) for s_expr in s_expr_lst[1:]
    ]
    with open(forge_file_path, 'w') as forge_file:
        transcribe_obj = new_transcribe.Transcribe_obj(forge_file)
        with open(base_file_path) as base_file:
            transcribe_obj.import_file(base_file)
        with open(extra_func_path) as extra_func_file:
            transcribe_obj.import_file(extra_func_file)
        new_transcribe.transcribe_protocol(protocol, transcribe_obj)
        for skel_indx, skeleton in enumerate(skeletons):
            new_transcribe.transcribe_skeleton(skeleton, protocol,
                                               transcribe_obj, skel_indx)
