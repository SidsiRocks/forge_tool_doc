option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

hweng_chen_splice_attack: run {
    wellformed

    exec_hweng_chen_splice_client
    exec_hweng_chen_splice_server
    exec_hweng_chen_splice_authority

    constrain_skeleton_hweng_chen_splice_0
    // constrain_skeleton_attack1_1

    no (hweng_chen_splice_client.hweng_chen_splice_client_c & Attacker)
    no (hweng_chen_splice_client.hweng_chen_splice_client_s & Attacker)
    no (hweng_chen_splice_client.hweng_chen_splice_client_as & Attacker)

    no (hweng_chen_splice_server.hweng_chen_splice_server_c & Attacker)
    no (hweng_chen_splice_server.hweng_chen_splice_server_s & Attacker)
    no (hweng_chen_splice_server.hweng_chen_splice_server_as & Attacker)

    no (hweng_chen_splice_authority.hweng_chen_splice_authority_c & Attacker)
    no (hweng_chen_splice_authority.hweng_chen_splice_authority_s & Attacker)
    no (hweng_chen_splice_authority.hweng_chen_splice_authority_as & Attacker)


    no (hweng_chen_splice_client.agent & hweng_chen_splice_server.agent)
    no (hweng_chen_splice_client.agent & hweng_chen_splice_authority.agent)
    no (hweng_chen_splice_server.agent & hweng_chen_splice_authority.agent)

    no (hweng_chen_splice_client.agent & Attacker)
    no (hweng_chen_splice_server.agent & Attacker)
    no (hweng_chen_splice_authority.agent & Attacker)


} for {
    next is linear
    mt_next is linear
    honest_run_bounds
    // attack1_bounds
}