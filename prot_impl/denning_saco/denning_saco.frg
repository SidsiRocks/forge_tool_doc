option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

denning_saco_honest_run: run {
    wellformed

    exec_denning_saco_init
    exec_denning_saco_resp
    exec_denning_saco_server

    // constrain_skeleton_denning_saco_0

    constrain_skeleton_attack_1

    // denning_saco_init.denning_saco_init_a != Attacker
    // denning_saco_init.denning_saco_init_b != Attacker
    // denning_saco_init.denning_saco_init_s != Attacker

    // denning_saco_resp.denning_saco_resp_a != Attacker
    // denning_saco_resp.denning_saco_resp_b != Attacker
    // denning_saco_resp.denning_saco_resp_s != Attacker

    // denning_saco_server.denning_saco_server_a != Attacker
    // denning_saco_server.denning_saco_server_b != Attacker
    // denning_saco_server.denning_saco_server_s != Attacker

    no (denning_saco_init.denning_saco_init_a & Attacker)
    no (denning_saco_init.denning_saco_init_b & Attacker)
    no (denning_saco_init.denning_saco_init_s & Attacker)

    no (denning_saco_resp.denning_saco_resp_a & Attacker)
    no (denning_saco_resp.denning_saco_resp_b & Attacker)
    no (denning_saco_resp.denning_saco_resp_s & Attacker)

    no (denning_saco_server.denning_saco_server_a & Attacker)
    no (denning_saco_server.denning_saco_server_b & Attacker)
    no (denning_saco_server.denning_saco_server_s & Attacker)

    not Attacker in (denning_saco_init + denning_saco_resp + denning_saco_server).agent

    no (denning_saco_init.agent & denning_saco_resp.agent)
    no (denning_saco_resp.agent & denning_saco_server.agent)
    no (denning_saco_server.agent & denning_saco_init.agent)

    no (Attacker.(KeyPairs.ltks))
    no (KeyPairs.ltks[Attacker])

    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)))
} for {
    next is linear
    mt_next is linear
    // honest_run_bounds
    attack_bounds
}