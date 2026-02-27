option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

pred attacker_learns2[d: mesg] {
  d in Attacker.learned_times.Timeslot
}

pred self_names_constraint{
    all arbitrary_init_tmn : tmn_init | {
        arbitrary_init_tmn.tmn_init_a = arbitrary_init_tmn.agent
    }
    all arbitrary_resp_tmn : tmn_resp | {
        arbitrary_resp_tmn.tmn_resp_b = arbitrary_resp_tmn.agent
    }
    all arbitrary_server_tmn : tmn_server | {
        arbitrary_server_tmn.tmn_server_s = arbitrary_server_tmn.agent
    }
}
pred not_talking_with_attacker{
    all arbitrary_init_tmn : tmn_init | {
        arbitrary_init_tmn.tmn_init_a != Attacker
        arbitrary_init_tmn.tmn_init_b != Attacker
        arbitrary_init_tmn.tmn_init_s != Attacker
    }
    all arbitrary_resp_tmn : tmn_resp | {
        arbitrary_resp_tmn.tmn_resp_a != Attacker
        arbitrary_resp_tmn.tmn_resp_b != Attacker
        arbitrary_resp_tmn.tmn_resp_s != Attacker
    }
    all arbitrary_server_tmn : tmn_server | {
        arbitrary_server_tmn.tmn_server_a != Attacker
        arbitrary_server_tmn.tmn_server_b != Attacker
        arbitrary_server_tmn.tmn_server_s != Attacker
    }
}

pred all_distinct_agents{
    no (tmn_init.agent & tmn_resp.agent)
    no (tmn_resp.agent & tmn_server.agent)
    no (tmn_server.agent & tmn_init.agent)
}
pred gen_honest_run{
    self_names_constraint
    not_talking_with_attacker
    all_distinct_agents
}
pred cannot_gen_privk{
    -- no private key can be generated
    no (PrivateKey & ((name.generated_times).Timeslot))
}
pred gen_attack{
    self_names_constraint
    cannot_gen_privk
    tmn_resp.tmn_resp_a != Attacker
    tmn_resp.tmn_resp_s != Attacker
    attacker_learns2[tmn_resp.tmn_resp_Kb]
}

tmn_attack : run {

  wellformed

  exec_tmn_init
  exec_tmn_resp
  exec_tmn_server

  -- constrain_skeleton_tmn_0

  -- honest participants
  tmn_init.agent != Attacker
  tmn_resp.agent != Attacker
  tmn_server.agent != Attacker

  -- tmn_init.tmn_init_a != tmn_init.tmn_init_b
  -- tmn_init.tmn_init_a != tmn_init.tmn_init_s
  -- tmn_init.tmn_init_b != tmn_init.tmn_init_s

  -- gen_honest_run
  -- secrecy violation
  gen_attack
} for {
  next is linear
  alt_tmn_small
}