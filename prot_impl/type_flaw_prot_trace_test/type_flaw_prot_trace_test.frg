option run_sterling "../../crypto_viz_text_seq.js"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B

    constrain_skeleton_type_flaw_prot_0
    let A = type_flaw_prot_A | { let B = type_flaw_prot_B | {
        A.agent != B.agent and A.agent != Attacker and B.agent != Attacker
        A.type_flaw_prot_A_b != Attacker
        -- corrected_attacker_learns[A.type_flaw_prot_A_n]
    } }

} for
    exactly 6 Timeslot,exactly 19 mesg,exactly 19 text,
    exactly 18 atomic,exactly 1 seq,
    exactly 6 Key,exactly 6 akey,exactly 0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,
    exactly 3 name,exactly 8 Ciphertext,exactly 1 nonce,
    exactly 1 KeyPairs,exactly 1 type_flaw_prot_A,
    exactly 2 type_flaw_prot_B,
    4 Int
for {next is linear}
