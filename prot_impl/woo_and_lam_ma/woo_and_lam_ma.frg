option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

woo_and_lam_ma_honest_run: run {
    wellformed 

    exec_woo_and_lam_ma_init
    exec_woo_and_lam_ma_server
    exec_woo_and_lam_ma_resp

    constrain_skeleton_woo_and_lam_ma_0

    no (woo_and_lam_ma_init.woo_and_lam_ma_init_p & Attacker)
    no (woo_and_lam_ma_init.woo_and_lam_ma_init_q & Attacker)
    no (woo_and_lam_ma_init.woo_and_lam_ma_init_s & Attacker)

    no (woo_and_lam_ma_server.woo_and_lam_ma_server_p & Attacker)
    no (woo_and_lam_ma_server.woo_and_lam_ma_server_q & Attacker)
    no (woo_and_lam_ma_server.woo_and_lam_ma_server_s & Attacker)

    no (woo_and_lam_ma_resp.woo_and_lam_ma_resp_p & Attacker)
    no (woo_and_lam_ma_resp.woo_and_lam_ma_resp_q & Attacker)
    no (woo_and_lam_ma_resp.woo_and_lam_ma_resp_s & Attacker)

    no (woo_and_lam_ma_init.agent & woo_and_lam_ma_server.agent)
    no (woo_and_lam_ma_init.agent & woo_and_lam_ma_resp.agent)
    no (woo_and_lam_ma_server.agent & woo_and_lam_ma_resp.agent)

    not Attacker in (woo_and_lam_ma_init + woo_and_lam_ma_server + woo_and_lam_ma_resp).agent

    all x, y: name | woo_and_lam_ma_server.woo_and_lam_ma_server_Kpq != x.(KeyPairs.ltks)[y]
} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}