option run_sterling "../../crypto_viz_seq_hash.js"

hash_term_test : run {
    wellformed
    exec_hash_term_test_A
    exec_hash_term_test_B
    constrain_skeleton_hash_term_test_0

}for
    exactly 4 Timeslot,17 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 3 text,exactly 2 Ciphertext,
    exactly 1 hash_term_test_A,exactly 1 hash_term_test_B,
    3 Int
for {next is linear}
