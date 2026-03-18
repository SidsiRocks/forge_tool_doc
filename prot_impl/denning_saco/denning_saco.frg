option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

denning_saco_attack: run {
    wellformed

    exec_denning_saco_init
    exec_denning_saco_resp
    exec_denning_saco_server

    denning_saco_init.agent != Attacker
    denning_saco_resp.agent != Attacker
    denning_saco_server.agent != Attacker

    denning_saco_init.agent != denning_saco_resp.agent
    denning_saco_resp.agent != denning_saco_server.agent
    denning_saco_server.agent != denning_saco_init.agent
} for {
    next is linear
    honest_run_bounds
}