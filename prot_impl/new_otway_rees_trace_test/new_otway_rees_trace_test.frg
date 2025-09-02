option run_sterling "../../crypto_viz_seq.js"

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce


new_ootway_prot_run : run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S
    constrain_skeleton_ootway_rees_0
    let A = ootway_rees_A | { let B = ootway_rees_B | {
    let S = ootway_rees_S | {
        (A.agent != Attacker) and (B.agent != Attacker) and (S.agent != Attacker)
        (A.agent != B.agent) and (A.agent != S.agent) and (B.agent != S.agent)
    let A_a = ootway_rees_A_a | { let A_b = ootway_rees_A_b | {
    let A_s = ootway_rees_A_s | {
        (A.A_a = A.agent) and (A.A_b = B.agent) and (A.A_s = S.agent)
    } } }

    let B_a = ootway_rees_B_a | { let B_b = ootway_rees_B_b | {
    let B_s = ootway_rees_B_s | {
        (B.B_a = A.agent) and (B.B_b = B.agent) and (B.B_s = S.agent)
    } } }

    let S_a = ootway_rees_S_a | { let S_b = ootway_rees_S_b | {
    let S_s = ootway_rees_S_s | {
        (S.S_a = A.agent) and (S.S_b = B.agent) and (S.S_s = S.agent)
    } } }

    let first_a_s_mesg = ootway_rees_B_first_a_s_mesg | {
        first_a_s_mesg in Ciphertext
        first_a_s_mesg.encryptionKey = getLTK[A.agent,S.agent]
        inds[first_a_s_mesg.plaintext] = 0+1+2+3
        (first_a_s_mesg.plaintext)[0] = A.ootway_rees_A_na
        (first_a_s_mesg.plaintext)[1] = A.ootway_rees_A_m
        (first_a_s_mesg.plaintext)[2] = A.ootway_rees_A_a
        (first_a_s_mesg.plaintext)[3] = A.ootway_rees_A_b
    }

    } } }
} for
    exactly 8 Timeslot,exactly 24 mesg,exactly 24 text,exactly 24 atomic,
    exactly 7 Key,exactly 0 akey,exactly 7 skey,exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 4 name,exactly 9 Ciphertext,exactly 4 nonce,exactly 1 KeyPairs,
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S
for { next is linear }
