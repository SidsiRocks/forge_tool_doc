option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

clark_jacob_splice_attack: run {
    wellformed

    exec_clark_jacob_splice_client
    exec_clark_jacob_splice_server
    exec_clark_jacob_splice_authority

    constrain_skeleton_clark_jacob_splice_0
    // constrain_skeleton_attack1_1

    no (clark_jacob_splice_client.clark_jacob_splice_client_c & Attacker)
    no (clark_jacob_splice_client.clark_jacob_splice_client_s & Attacker)
    no (clark_jacob_splice_client.clark_jacob_splice_client_as & Attacker)

    no (clark_jacob_splice_server.clark_jacob_splice_server_c & Attacker)
    no (clark_jacob_splice_server.clark_jacob_splice_server_s & Attacker)
    no (clark_jacob_splice_server.clark_jacob_splice_server_as & Attacker)

    no (clark_jacob_splice_authority.clark_jacob_splice_authority_c & Attacker)
    no (clark_jacob_splice_authority.clark_jacob_splice_authority_s & Attacker)
    no (clark_jacob_splice_authority.clark_jacob_splice_authority_as & Attacker)


    no (clark_jacob_splice_client.agent & clark_jacob_splice_server.agent)
    no (clark_jacob_splice_client.agent & clark_jacob_splice_authority.agent)
    no (clark_jacob_splice_server.agent & clark_jacob_splice_authority.agent)

    no (clark_jacob_splice_client.agent & Attacker)
    no (clark_jacob_splice_server.agent & Attacker)
    no (clark_jacob_splice_authority.agent & Attacker)


} for {
    next is linear
    mt_next is linear
    honest_run_bounds
    // attack1_bounds
}