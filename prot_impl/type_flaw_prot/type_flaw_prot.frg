option run_sterling "../../crypto_viz_text_seq.js"
-- option verbose 10
-- option solver "../../../../../../../../../usr/bin/minisat"
option engine_verbosity 3

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B
    constrain_skeleton_type_flaw_prot_0
}for
    exactly 4 Timeslot,13 mesg,13 text,13 atomic,0 seq,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 3 Ciphertext,exactly 1 nonce,
    exactly 1 type_flaw_prot_A,exactly 1 type_flaw_prot_B,
    3 Int
for {next is linear}
