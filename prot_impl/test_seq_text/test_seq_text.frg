option run_sterling "../../crypto_viz_seq.js"

test_seq_text_run : run {
    wellformed

    exec_test_seq_text_A
    exec_test_seq_text_B

    test_seq_text_A.test_seq_text_A_a = test_seq_text_A.agent   
    test_seq_text_A.test_seq_text_A_b = test_seq_text_B.agent   

    test_seq_text_B.test_seq_text_B_a = test_seq_text_A.agent   
    test_seq_text_B.test_seq_text_B_b = test_seq_text_B.agent

    test_seq_text_A.test_seq_text_A_n2 in seq
}
for
    exactly 13 mesg,exactly 13 text,
    exactly 13 atomic,exactly 6 Key,exactly 3 name,
    exactly 3 Ciphertext,exactly 1 nonce,exactly 6 Key,
    exactly 6 akey,exactly 0 skey,
    exactly 3 PublicKey,exactly 3 PrivateKey,exactly 1 KeyPairs,
    exactly 1 test_seq_text_A,exactly 1 test_seq_text_B,
    4 Int
for {next is linear}