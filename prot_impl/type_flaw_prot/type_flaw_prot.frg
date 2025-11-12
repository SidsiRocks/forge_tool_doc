-- option run_sterling "../../crypto_viz_text_seq.js"
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
--option verbose 5

-- option solver "../../../../../../../../../usr/bin/minisat"
--option engine_verbosity 3

--option solver MiniSatProver
--option logtranslation 1
--option coregranularity 1
--option core_minimization rce

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B
    constrain_skeleton_type_flaw_prot_0

    no (type_flaw_prot_A.agent & type_flaw_prot_B.agent)
    not (Attacker in (type_flaw_prot_A + type_flaw_prot_B).agent)

    -- this ensures neither initiates agent with attacker so
    -- should would imply an honest run
    -- not (Attacker in type_flaw_prot_A.type_flaw_prot_A_b + type_flaw_prot_B.type_flaw_prot_B_a)

    -- A shouldn't be talking to Attacker
    -- not (Attacker in type_flaw_prot_A.type_flaw_prot_A_b)
    one type_flaw_prot_B.agent
    type_flaw_prot_A.type_flaw_prot_A_b = type_flaw_prot_B.agent

    corrected_attacker_learns[type_flaw_prot_A.type_flaw_prot_A_n]

    -- trace constraint should have different B1 and B2
    -- skeleton_type_flaw_prot_0.skeleton_type_flaw_prot_0_B1 != skeleton_type_flaw_prot_0.skeleton_type_flaw_prot_0_B2
}for
--    exactly 4 Timeslot,13 mesg,13 text,13 atomic,0 seq,
--    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
--    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
--    exactly 3 name,exactly 3 Ciphertext,exactly 1 nonce,
--    exactly 1 type_flaw_prot_A,exactly 1 type_flaw_prot_B,
--    3 Int
-- for {next is linear}
--    exactly 3 Int
--    for{
--        next is linear
--        honest_run_bounds
--    }
   exactly 3 Int
   for{
         next is linear
--         attack_run_bounds
         smaller_attack_bound
--         larger_attack_bound
   }
