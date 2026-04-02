option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

kao_chow_v2_honest_run: run {
    wellformed

    exec_kao_chow_v2_init
    exec_kao_chow_v2_server
    exec_kao_chow_v2_resp

    constrain_skeleton_kao_chow_v2_0

    kao_chow_v2_init.kao_chow_v2_init_b != Attacker
    kao_chow_v2_init.kao_chow_v2_init_s != Attacker
    kao_chow_v2_init.kao_chow_v2_init_a != Attacker

    kao_chow_v2_server.kao_chow_v2_server_b != Attacker
    kao_chow_v2_server.kao_chow_v2_server_a != Attacker
    kao_chow_v2_server.kao_chow_v2_server_s != Attacker

    kao_chow_v2_resp.kao_chow_v2_resp_a != Attacker
    kao_chow_v2_resp.kao_chow_v2_resp_s != Attacker
    kao_chow_v2_resp.kao_chow_v2_resp_b != Attacker

    kao_chow_v2_init.agent != kao_chow_v2_server.agent
    kao_chow_v2_init.agent != kao_chow_v2_resp.agent
    kao_chow_v2_server.agent != kao_chow_v2_resp.agent

    not Attacker in (kao_chow_v2_init + kao_chow_v2_server + kao_chow_v2_resp).agent

    
    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)) )

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}