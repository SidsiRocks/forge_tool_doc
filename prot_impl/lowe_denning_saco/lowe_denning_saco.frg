option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

lowe_denning_saco_honest_run: run {
    wellformed

    exec_lowe_denning_saco_init
    exec_lowe_denning_saco_resp
    exec_lowe_denning_saco_server

    constrain_skeleton_lowe_denning_saco_0

    lowe_denning_saco_init.lowe_denning_saco_init_a != Attacker
    lowe_denning_saco_init.lowe_denning_saco_init_b != Attacker
    lowe_denning_saco_init.lowe_denning_saco_init_s != Attacker

    lowe_denning_saco_resp.lowe_denning_saco_resp_a != Attacker
    lowe_denning_saco_resp.lowe_denning_saco_resp_b != Attacker
    lowe_denning_saco_resp.lowe_denning_saco_resp_s != Attacker

    lowe_denning_saco_server.lowe_denning_saco_server_a != Attacker
    lowe_denning_saco_server.lowe_denning_saco_server_b != Attacker
    lowe_denning_saco_server.lowe_denning_saco_server_s != Attacker

    lowe_denning_saco_init.agent != lowe_denning_saco_resp.agent
    lowe_denning_saco_resp.agent != lowe_denning_saco_server.agent
    lowe_denning_saco_server.agent != lowe_denning_saco_init.agent

    not Attacker in (lowe_denning_saco_init + lowe_denning_saco_resp + lowe_denning_saco_server).agent

    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)))
} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}