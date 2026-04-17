option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

woo_and_lam_pi_honest_run: run {
    wellformed 

    exec_woo_and_lam_pi_init
    exec_woo_and_lam_pi_server
    exec_woo_and_lam_pi_resp

    constrain_skeleton_woo_and_lam_pi_0

    no (woo_and_lam_pi_init.woo_and_lam_pi_init_a & Attacker)
    no (woo_and_lam_pi_init.woo_and_lam_pi_init_b & Attacker)
    no (woo_and_lam_pi_init.woo_and_lam_pi_init_s & Attacker)

    no (woo_and_lam_pi_server.woo_and_lam_pi_server_a & Attacker)
    no (woo_and_lam_pi_server.woo_and_lam_pi_server_b & Attacker)
    no (woo_and_lam_pi_server.woo_and_lam_pi_server_s & Attacker)

    no (woo_and_lam_pi_resp.woo_and_lam_pi_resp_a & Attacker)
    no (woo_and_lam_pi_resp.woo_and_lam_pi_resp_b & Attacker)
    no (woo_and_lam_pi_resp.woo_and_lam_pi_resp_s & Attacker)

    no (woo_and_lam_pi_init.agent & woo_and_lam_pi_server.agent)
    no (woo_and_lam_pi_init.agent & woo_and_lam_pi_resp.agent)
    no (woo_and_lam_pi_server.agent & woo_and_lam_pi_resp.agent)

    not Attacker in (woo_and_lam_pi_init + woo_and_lam_pi_server + woo_and_lam_pi_resp).agent
} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}