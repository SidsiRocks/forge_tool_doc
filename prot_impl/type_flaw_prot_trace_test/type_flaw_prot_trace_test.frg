option run_sterling "../../crypto_viz_text_seq.js"

type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B
    constrain_skeleton_type_flaw_prot_0
} for
    exactly 4 Timeslot,exactly 13 mesg,exactly 13 atomic,
    exactly 6 Key,exactly 6 akey,exactly 0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,exactly 3 name,
    exactly 3 Ciphertext,exactly 1 nonce,exactly 1 KeyPairs,
    exactly 1 type_flaw_prot_A,exactly 1 type_flaw_prot_B,
    4 Int
for {next is linear}
