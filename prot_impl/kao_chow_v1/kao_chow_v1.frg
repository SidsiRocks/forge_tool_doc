option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

kao_chow_v1_honest_run: run {
    wellformed

    exec_kao_chow_v1_init
    exec_kao_chow_v1_server
    exec_kao_chow_v1_resp

    // constrain_skeleton_kao_chow_v1_0
    constrain_skeleton_attack_1

    kao_chow_v1_init.kao_chow_v1_init_b != Attacker
    kao_chow_v1_init.kao_chow_v1_init_s != Attacker
    kao_chow_v1_init.kao_chow_v1_init_a != Attacker

    kao_chow_v1_server.kao_chow_v1_server_b != Attacker
    kao_chow_v1_server.kao_chow_v1_server_a != Attacker
    kao_chow_v1_server.kao_chow_v1_server_s != Attacker

    kao_chow_v1_resp.kao_chow_v1_resp_a != Attacker
    kao_chow_v1_resp.kao_chow_v1_resp_s != Attacker
    kao_chow_v1_resp.kao_chow_v1_resp_b != Attacker

    kao_chow_v1_init.agent != kao_chow_v1_server.agent
    kao_chow_v1_init.agent != kao_chow_v1_resp.agent
    kao_chow_v1_server.agent != kao_chow_v1_resp.agent

    not Attacker in (kao_chow_v1_init + kao_chow_v1_server + kao_chow_v1_resp).agent

    
    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)) )

    kao_chow_v1_server.kao_chow_v1_server_Kab
    in Attacker.learned_times.Timeslot

    all x: name, y: name | kao_chow_v1_server.kao_chow_v1_server_Kab != x.(KeyPairs.ltks)[y]

} for {
    next is linear
    mt_next is linear
    // honest_run_bounds
    attack_bounds
}