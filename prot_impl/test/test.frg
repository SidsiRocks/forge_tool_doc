option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

needham_schroeder_sym_key_honest_run: run {
    wellformed

    exec_needham_schroeder_sym_key_init
    exec_needham_schroeder_sym_key_server
    // exec_needham_schroeder_sym_key_resp

    constrain_skeleton_needham_schroeder_sym_key_0

    // no (needham_schroeder_sym_key_init.agent & needham_schroeder_sym_key_server.agent)

    // needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_a != needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_b

    needham_schroeder_sym_key_init.agent != needham_schroeder_sym_key_server.agent
    needham_schroeder_sym_key_init.agent != needham_schroeder_sym_key_resp.agent
    needham_schroeder_sym_key_server.agent != needham_schroeder_sym_key_resp.agent

    not Attacker in (needham_schroeder_sym_key_init + needham_schroeder_sym_key_server + needham_schroeder_sym_key_resp).agent

    // no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)) )

    // needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_Kab in Attacker.learned_times.Timeslot

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}