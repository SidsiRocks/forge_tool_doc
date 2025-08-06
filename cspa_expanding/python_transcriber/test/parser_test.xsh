#!/usr/bin/env xonsh
import sys
import os
import io
import sexpdata
sys.path.append("..")
from parser import *
from typing import List,Tuple
from type_and_helpers import *
from contextlib import redirect_stdout

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def create_var_dict(var_and_type:List[Tuple[str,VarType]]):
    result:VarMap = {}
    for variable_name,variable_type in var_and_type:
        if variable_name in result:
            raise Exception(f"{variable_name} is repeated in {var_and_type}")
        result[variable_name] = Variable(variable_name,variable_type)
    return result
def pp_sexp_in_file(file_name:str):
    txt = $(cat @(file_name) | sexp pp)
    with open(file_name,'w') as file:
        print(txt,file=file)
def show_diff(file_name_1,file_name_2):
    has_diff = $(diff -q @(file_name_1) @(file_name_2))
    if len(has_diff) != 0:
        num_cols,_ = os.get_terminal_size()
        padding = max(num_cols - len(file_name_1) - len(file_name_2),1)
        header = ''.join([file_name_1,' '*padding,file_name_2])
        print(header)
        $[diff -wy @(file_name_1) @(file_name_2)]
        return True
    return False
def run_sexp_expect_test(test_function,test_name:str,expected_output:str):
    temp_test_file_name = f"temp_{test_name}.txt"
    temp_result_file_name = f"temp_expected_output.txt"
    with open(temp_test_file_name,'w') as temp_test_file,redirect_stdout(temp_test_file):
        test_function()
    pp_sexp_in_file(temp_test_file_name)
    with open(temp_result_file_name,'w') as temp_result_file:
        print(expected_output,file=temp_result_file)
    pp_sexp_in_file(temp_result_file_name)
    has_diff = show_diff(temp_test_file_name,temp_result_file_name)
    if has_diff:
        print(f"{test_name} has {bcolors.FAIL}FAILED{bcolors.ENDC}")
    else:
        print(f"{test_name} has {bcolors.OKGREEN}PASSED{bcolors.ENDC}")
def parse_test_case(str_to_parse,parse_function):
    print(parse_function(sexpdata.loads(str_to_parse)))

def valid_parse_test():
    var_dict = [ ("name1",VarType.NAME),("name2",VarType.NAME) ]
    key_parse_func = lambda sexpr:parse_key_term(sexpr,create_var_dict(var_dict))
    parse_test_case("(pubk name1)",key_parse_func)
    parse_test_case("(privk name1)",key_parse_func)
    parse_test_case("(ltk name1 name2)",key_parse_func)
    # parse_test_case("(a b name) (c d text) (e f skey) (g h akey)")
    # parse_test_case("(vars (a b name) (c d text) (e f skey) (g h akey))")
    # parse_test_case("a",parse_message_term)

    var_dict = [("f",VarType.SKEY),("d",VarType.AKEY),("a",VarType.NAME),("b",VarType.NAME),("c",VarType.NAME),("e",VarType.NAME)]
    msg_parse_func = lambda sexpr:parse_message_term(sexpr,create_var_dict(var_dict))
    parse_test_case("(cat a b c)",msg_parse_func)
    parse_test_case("(enc d e f)",msg_parse_func)
    parse_test_case("(cat a (enc d e f) c)",msg_parse_func)
    parse_test_case("(cat a (cat b c d) e)",msg_parse_func)
    parse_test_case("(cat a (ltk a b) (pubk a))",msg_parse_func)
    parse_test_case("(enc a b c (ltk a b))",msg_parse_func)
    parse_test_case("(enc a b c (privk a))",msg_parse_func)
    parse_test_case("(enc a (cat a b c) (ltk a b))",msg_parse_func)
def invalid_key_parse_test():
    var_dict = []
    parse_func = lambda sexpr:parse_key_term(sexpr,create_var_dict(var_dict))
    parse_test_case("(pubk name1)",parse_func)
expect_test="""
(pubk name1)
(privk name1)
(ltk name1 name2)
(cat a b c)
(enc d e f)
(cat a (enc d e f) c)
(cat a b c d e)
(cat a (ltk a b) (pubk a))
(enc a b c (ltk a b))
(enc a b c (privk a))
(enc a a b c (ltk a b))
"""
run_sexp_expect_test(valid_parse_test,"valid_key_parse_test",expect_test)
#show_diff("parser_test.xsh","temp_expected_output.txt")
