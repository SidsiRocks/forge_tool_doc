option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

splice_attack: run {
    wellformed

    exec_splice_client
    exec_splice_server
    exec_splice_authority

    // constrain_skeleton_splice_0
    constrain_skeleton_attack1_1

    no (splice_client.splice_client_c & Attacker)
    no (splice_client.splice_client_s & Attacker)
    no (splice_client.splice_client_as & Attacker)

    no (splice_server.splice_server_c & Attacker)
    no (splice_server.splice_server_s & Attacker)
    no (splice_server.splice_server_as & Attacker)

    no (splice_authority.splice_authority_c & Attacker)
    no (splice_authority.splice_authority_s & Attacker)
    no (splice_authority.splice_authority_as & Attacker)


    no (splice_client.agent & splice_server.agent)
    no (splice_client.agent & splice_authority.agent)
    no (splice_server.agent & splice_authority.agent)

    no (splice_client.agent & Attacker)
    no (splice_server.agent & Attacker)
    no (splice_authority.agent & Attacker)


} for {
    next is linear
    mt_next is linear
    // honest_run_bounds
    attack1_bounds
}