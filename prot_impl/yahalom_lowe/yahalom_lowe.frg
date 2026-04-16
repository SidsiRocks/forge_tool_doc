option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

yahalom_lowe_honest_run: run {
    wellformed

    exec_yahalom_lowe_init
    exec_yahalom_lowe_server
    exec_yahalom_lowe_resp

    constrain_skeleton_yahalom_lowe_0

    no (yahalom_lowe_init.agent & yahalom_lowe_server.agent)
    no (yahalom_lowe_init.agent & yahalom_lowe_resp.agent)
    no (yahalom_lowe_server.agent & yahalom_lowe_resp.agent)

    not Attacker in (yahalom_lowe_init + yahalom_lowe_server + yahalom_lowe_resp).agent

    all x, y: name | yahalom_lowe_server.yahalom_lowe_server_Kab != x.(KeyPairs.ltks)[y]

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}