small_test_run : run {
    small_test_A.agent != Attacker
    small_test_B.agent != Attacker

    small_test_A.small_test_A_a = small_test_A.agent
    small_test_A.small_test_A_b = small_test_B.agent

    small_test_B.small_test_B_a = small_test_A.agent
    small_test_B.small_test_B_b = small_test_B.agent

    wellformed 
    exec_small_test_A
    exec_small_test_B
}for 
    exactly 4 Timeslot,16 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,exactly 0 skey,
    exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 2 text,exactly 0 Ciphertext,
    exactly 1 small_test_A,exactly 1 small_test_B,
    3 Int
for {next is linear}