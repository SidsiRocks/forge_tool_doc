option run_sterling "../../crypto_viz_seq.js"

new_ootway_prot_run : run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_B
    constrain_skeleton_ootway_rees_0
} for
    exactly 8 Timeslot,exactly 20 mesg,exactly 20 text,exactly 20 atomic,
    exactly 3 Key,exactly 0 akey,exactly 3 skey,exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 4 name,exactly 9 Ciphertext,exactly 4 nonce,exactly 1 KeyPairs,
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S,
    4 Int
for {next is linear}
