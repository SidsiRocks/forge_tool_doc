option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

yahalom_paulson_honest_run: run {
    wellformed

    exec_yahalom_paulson_init
    exec_yahalom_paulson_server
    exec_yahalom_paulson_resp

    constrain_skeleton_yahalom_paulson_0

    no (yahalom_paulson_init.agent & yahalom_paulson_server.agent)
    no (yahalom_paulson_init.agent & yahalom_paulson_resp.agent)
    no (yahalom_paulson_server.agent & yahalom_paulson_resp.agent)

    not Attacker in (yahalom_paulson_init + yahalom_paulson_server + yahalom_paulson_resp).agent

    all x, y: name | yahalom_paulson_server.yahalom_paulson_server_Kab != x.(KeyPairs.ltks)[y]

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}