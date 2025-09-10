option run_sterling "../../crypto_viz_text_seq.js"
option engine_verbosity 3

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

-- Below constraints generate an honest run
-- type_flaw_prot_run : run {
--    wellformed
--    exec_type_flaw_prot_A
--    exec_type_flaw_prot_B
--    constrain_skeleton_type_flaw_prot_0
--}for
--    exactly 4 Timeslot,14 mesg,14 text,13 atomic,1 seq,
--    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
--    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
--    exactly 3 name,exactly 3 Ciphertext,exactly 1 nonce,
--    exactly 1 type_flaw_prot_A,exactly 1 type_flaw_prot_B,
--    3 Int
--for {next is linear}

pred non_orig[m:mesg]{
    no aStrand : strand | {
        originates[aStrand,m] or generates[aStrand,m]
    }
}


type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B
    constrain_skeleton_type_flaw_prot_1

    type_flaw_prot_A.type_flaw_prot_A_b != Attacker

    let skel_1 = skeleton_type_flaw_prot_1 | {
        let B1 = skeleton_type_flaw_prot_1_B1 | {
            let B2 = skeleton_type_flaw_prot_1_B2 | {
                skel_1.B1 != skel_1.B2
                (skel_1.B1).agent = (skel_1.B2).agent
                non_orig[getPRIVK[(skel_1.B1).agent]]
            }
        }
    }

    corrected_attacker_learns[type_flaw_prot_A.type_flaw_prot_A_n]
}for
    exactly 6 Timeslot,20 mesg,20 text,17 atomic,3 seq,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 7 Ciphertext,exactly 1 nonce,
    exactly 1 type_flaw_prot_A,exactly 2 type_flaw_prot_B,
    3 Int
for {next is linear}

