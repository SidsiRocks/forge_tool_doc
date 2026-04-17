option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

woo_and_lam_pi2_honest_run: run {
    wellformed 

    exec_woo_and_lam_pi2_init
    exec_woo_and_lam_pi2_server
    exec_woo_and_lam_pi2_resp

    constrain_skeleton_woo_and_lam_pi2_0

    no (woo_and_lam_pi2_init.woo_and_lam_pi2_init_a & Attacker)
    no (woo_and_lam_pi2_init.woo_and_lam_pi2_init_b & Attacker)
    no (woo_and_lam_pi2_init.woo_and_lam_pi2_init_s & Attacker)

    no (woo_and_lam_pi2_server.woo_and_lam_pi2_server_a & Attacker)
    no (woo_and_lam_pi2_server.woo_and_lam_pi2_server_b & Attacker)
    no (woo_and_lam_pi2_server.woo_and_lam_pi2_server_s & Attacker)

    no (woo_and_lam_pi2_resp.woo_and_lam_pi2_resp_a & Attacker)
    no (woo_and_lam_pi2_resp.woo_and_lam_pi2_resp_b & Attacker)
    no (woo_and_lam_pi2_resp.woo_and_lam_pi2_resp_s & Attacker)

    no (woo_and_lam_pi2_init.agent & woo_and_lam_pi2_server.agent)
    no (woo_and_lam_pi2_init.agent & woo_and_lam_pi2_resp.agent)
    no (woo_and_lam_pi2_server.agent & woo_and_lam_pi2_resp.agent)

    not Attacker in (woo_and_lam_pi2_init + woo_and_lam_pi2_server + woo_and_lam_pi2_resp).agent
} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}