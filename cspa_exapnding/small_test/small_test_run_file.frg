small_test_run : run {
    wellformed
    exec_small_test_A
    exec_small_test_B
}
for 
    exactly 4 Timeslot,16 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,exactly 0 skey,
    exactly 3 PublicKey, exactly 3 PrivateKey,
    exactly 3 name,exactly 2 text,exactly 0 Ciphertext,
    exactly 1 small_test_A,exactly 1 small_test_B,
    1 Int
for {next is linear}