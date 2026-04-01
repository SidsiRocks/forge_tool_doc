option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

denning_saco_attack: run {
    wellformed

    exec_denning_saco_init
    exec_denning_saco_resp
    exec_denning_saco_server

    constrain_skeleton_denning_saco_0

    not Attacker in (denning_saco_init + denning_saco_resp + denning_saco_server).agent

    denning_saco_init.agent != denning_saco_resp.agent
    denning_saco_resp.agent != denning_saco_server.agent
    denning_saco_server.agent != denning_saco_init.agent
} for {
    next is linear
    attack_bounds
}