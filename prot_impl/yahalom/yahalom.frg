option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

yahalom_honest_run: run {
    wellformed

    exec_yahalom_init
    exec_yahalom_server
    exec_yahalom_resp

    constrain_skeleton_yahalom_0

    no (yahalom_init.agent & yahalom_server.agent)
    no (yahalom_init.agent & yahalom_resp.agent)
    no (yahalom_server.agent & yahalom_resp.agent)

    not Attacker in (yahalom_init + yahalom_server + yahalom_resp).agent

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}