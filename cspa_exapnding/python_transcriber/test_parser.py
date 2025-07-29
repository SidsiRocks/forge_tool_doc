import parser
import sexpdata
import subprocess
from main import get_root_s_expr_lst, load_cspa_as_s_expr_new


def get_pp_sexp(sexp_str):
    return subprocess.getoutput(f"echo \"{sexp_str}\" | sexp pp")


def test_parse_role():
    role_string = """
(defrole init
    (vars (a b name) (n1 n2 text))
    (trace
        (send (enc n1 (pubk b)))
        (recv (enc n1 n2 (pubk a)))
        (send (enc n2 (pubk b)))
    )
)
    """
    role = parser.parse_role(sexpdata.loads(role_string))
    assert get_pp_sexp(f"{role}") == get_pp_sexp(role_string)


def remove_comments_from_file(rkt_file):
    for _ in rkt_file:
        break
    result = ""
    for line in rkt_file:
        if ";;" not in line:
            result += line
    return result


def helper_for_test_rkt_file(rkt_file_path):
    with open(rkt_file_path) as rkt_file:
        all_txt = remove_comments_from_file(rkt_file)
        s_expr_strs = get_root_s_expr_lst(all_txt)
        prot_str = s_expr_strs[0]
        skeleton_strs = s_expr_strs[1:]

        s_exprs = [sexpdata.loads(s_exp_str) for s_exp_str in s_expr_strs]
        protocol = parser.parse_protocol(s_exprs[0])
        skeletons = [
            parser.parse_skeleton(s_expr, protocol) for s_expr in s_exprs[1:]
        ]
        assert get_pp_sexp(f"{protocol}") == get_pp_sexp(prot_str)
        for skel_str, skeleton in zip(skeleton_strs, skeletons):
            assert get_pp_sexp(f"{skeleton}") == get_pp_sexp(skel_str)


#TODO: add other tests using the ideas from here
def test_addit_enc_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/additional_enc_test/addit_enc.rkt"
    )


def test_duplic_terms_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/diff_btwn_tools/duplic_terms.rkt"
    )


def test_enc_terms_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/diff_btwn_tools/enc_term.rkt")


def test_new_reorder_terms_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/diff_btwn_tools/new_reorder_terms.rkt"
    )


def test_reorder_terms_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/diff_btwn_tools/reorder_terms.rkt"
    )


def test_simple_enc_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/simple_enc_test/simple_enc.rkt"
    )


def test_small_test_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/small_test/small_test.rkt")


def test_msg_order_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/tests/msg_order_test/msg_order.rkt"
    )


def test_two_nonce_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/two_nonce/two_nonce.rkt")


def test_two_nonce_temp_parsing():
    helper_for_test_rkt_file(
        r"../../../forge_tool_doc/cspa_exapnding/two_nonce/two_nonce_temp.rkt")


def test_lowe_ns_parsing():
    helper_for_test_rkt_file(r"../../../forge_tool_doc/prot_impl/lowe_ns.rkt")


def test_ns_parsing():
    helper_for_test_rkt_file(r"../../../forge_tool_doc/prot_impl/ns.rkt")


def test_nspk_parsing():
    helper_for_test_rkt_file(r"../../../forge_tool_doc/prot_impl/nspk.rkt")
