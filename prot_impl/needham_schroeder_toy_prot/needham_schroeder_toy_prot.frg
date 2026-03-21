option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

needham_schroeder_toy_prot: run {
    wellformed

    exec_needham_schroeder_toy_prot_init
    exec_needham_schroeder_toy_prot_resp

    constrain_skeleton_needham_schroeder_toy_prot_0

    no (needham_schroeder_toy_prot_resp.agent & needham_schroeder_toy_prot_init.agent)

    not (Attacker in (needham_schroeder_toy_prot_init + needham_schroeder_toy_prot_resp).agent)

    not (Attacker in needham_schroeder_toy_prot_init.needham_schroeder_toy_prot_init_b)

    corrected_attacker_learns[needham_schroeder_toy_prot_init.needham_schroeder_toy_prot_init_n1]
} for {
    next is linear
    alt_single_session
}