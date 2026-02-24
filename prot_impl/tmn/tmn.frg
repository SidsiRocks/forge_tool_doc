option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

pred corrected_attacker_learns[d: mesg] {
  d in Attacker.learned_times.Timeslot
}


tmn_attack : run {

  wellformed

  exec_tmn_A
  exec_tmn_B
  exec_tmn_S

  constrain_skeleton_tmn_0

  -- secrecy violation
  corrected_attacker_learns[tmn_A.tmn_A_Kb]

} for {
  next is linear
  alt_tmn_small
}