option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose

-- option logtranslation 1
-- option coregranularity 1
-- option core_minimization rce

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

ootway_rees_prot_run: run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S
    constrain_skeleton_honest_run_with_1_ABS_0

    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_m

    ootway_rees_A.agent != ootway_rees_B.agent
    ootway_rees_A.agent != ootway_rees_S.agent
    ootway_rees_B.agent != ootway_rees_S.agent

    ootway_rees_A.ootway_rees_A_kab != ootway_rees_S.ootway_rees_S_kab
}for
  exactly 4 Int
  for{
      next is linear
      mt_next is linear
      honest_run_bounds
  }
--    exactly 8 Timeslot,
--    exactly 37 mesg,
--    exactly 4 Key,exactly 3 name,exactly 8 Ciphertext,exactly 6 text,exactly 16 tuple,
--    exactly 0 akey,exactly 4 skey,exactly 1 Attacker,
--    exactly 0 PublicKey,exactly 0 PrivateKey,
--    exactly 2 Microtick,
--    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,exactly 1 ootway_rees_S,
--    exactly 4 Int
--    for{
--        next is linear
--        mt_next is linear
--    }
