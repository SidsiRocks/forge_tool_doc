option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

pred attacker_learns2[d: mesg] {
  d in Attacker.learned_times.Timeslot
}


tmn_attack : run {

  wellformed

  exec_tmn_init
  exec_tmn_resp
  exec_tmn_server

  constrain_skeleton_tmn_0

  -- honest participants
  tmn_init.agent != Attacker
  tmn_resp.agent != Attacker
  tmn_server.agent != Attacker

  tmn_init.tmn_init_a != tmn_init.tmn_init_b
  tmn_init.tmn_init_a != tmn_init.tmn_init_s
  tmn_init.tmn_init_b != tmn_init.tmn_init_s

  -- secrecy violation
  attacker_learns2[tmn_init.tmn_init_Kb]

} for {
  next is linear
  alt_tmn_small
}