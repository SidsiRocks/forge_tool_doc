option run_sterling "../../crypto_viz_text_seq.js"
option engine_verbosity 3

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

nested_seq_test_run : run {
    wellformed
    exec_nested_seq_test_A
    exec_nested_seq_test_B
    constrain_skeleton_nested_seq_test_0
}for
    exactly 4 Timeslot,18 mesg,18 text,15 atomic,3 seq,
     exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
     exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
     exactly 3 name,exactly 5 Ciphertext,exactly 1 nonce,
     exactly 1 nested_seq_test_A,exactly 1 nested_seq_test_B,
     3 Int
for {next is linear}
