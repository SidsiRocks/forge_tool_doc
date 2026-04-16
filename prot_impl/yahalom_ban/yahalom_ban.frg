option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

yahalom_ban_honest_run: run {
    wellformed

    exec_yahalom_ban_init
    exec_yahalom_ban_server
    exec_yahalom_ban_resp

    constrain_skeleton_yahalom_ban_0

    no (yahalom_ban_init.agent & yahalom_ban_server.agent)
    no (yahalom_ban_init.agent & yahalom_ban_resp.agent)
    no (yahalom_ban_server.agent & yahalom_ban_resp.agent)

    not Attacker in (yahalom_ban_init + yahalom_ban_server + yahalom_ban_resp).agent

    all x, y: name | yahalom_ban_server.yahalom_ban_server_Kab != x.(KeyPairs.ltks)[y]

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}