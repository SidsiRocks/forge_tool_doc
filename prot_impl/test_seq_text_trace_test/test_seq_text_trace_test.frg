option run_sterling "../../crypto_viz_text_seq.js"

test_seq_text_run : run {
    wellformed
    exec_test_seq_text_A
    exec_test_seq_text_B
    constrain_skeleton_test_seq_text_0

    test_seq_text_A.test_seq_text_A_a = test_seq_text_A.agent
    test_seq_text_A.test_seq_text_A_b = test_seq_text_B.agent

    -- test_seq_text_B.test_seq_text_B_a = test_seq_text_A.agent
    -- test_seq_text_B.test_seq_text_B_b = test_seq_text_B.agent
    -- test_seq_text_A.test_seq_text_A_n2 in seq
    -- inds[test_seq_text_A.test_seq_text_A_n2.components] = 0+1
}for
    exactly 4 Timeslot,exactly 14 mesg,exactly 14 text,
    exactly 1 seq,exactly 13 atomic,exactly 6 Key,exactly 3 name,
    exactly 3 Ciphertext,exactly 1 nonce,exactly 6 akey,exactly 0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,exactly 1 KeyPairs,
    exactly 1 test_seq_text_A,exactly 1 test_seq_text_B,
    4 Int
for {next is linear}
