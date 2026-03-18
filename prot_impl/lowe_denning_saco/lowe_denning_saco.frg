option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

lowe_denning_saco_honest_run: run {
    wellformed

    exec_lowe_denning_saco_init
    exec_lowe_denning_saco_resp
    exec_lowe_denning_saco_server

    lowe_denning_saco_init.agent != Attacker
    lowe_denning_saco_resp.agent != Attacker
    lowe_denning_saco_server.agent != Attacker

    lowe_denning_saco_init.agent != lowe_denning_saco_resp.agent
    lowe_denning_saco_resp.agent != lowe_denning_saco_server.agent
    lowe_denning_saco_server.agent != lowe_denning_saco_init.agent
} for {
    next is linear
    honest_run_bounds
}