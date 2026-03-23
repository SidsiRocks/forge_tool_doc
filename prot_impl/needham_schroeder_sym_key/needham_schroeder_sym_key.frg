option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

needham_schroeder_sym_key_honest_run: run {
    wellformed

    exec_needham_schroeder_sym_key_init
    exec_needham_schroeder_sym_key_server
    exec_needham_schroeder_sym_key_resp

    constrain_skeleton_needham_schroeder_sym_key_0

    needham_schroeder_sym_key_init.agent != needham_schroeder_sym_key_server.agent
    needham_schroeder_sym_key_init.agent != needham_schroeder_sym_key_resp.agent
    needham_schroeder_sym_key_server.agent != needham_schroeder_sym_key_resp.agent

    not Attacker in (needham_schroeder_sym_key_init + needham_schroeder_sym_key_server + needham_schroeder_sym_key_resp).agent

} for {
    next is linear
    honest_run_bounds
}