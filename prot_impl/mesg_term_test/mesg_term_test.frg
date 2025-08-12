option run_sterling "../../crypto_viz_seq.js"

// TODO add something to auto generate common parts of base file
// end up making silly mistakes like not including pred weillformed
mesg_term_test_run : run {
    wellformed 

    exec_mesg_term_test_A
    exec_mesg_term_test_B

    mesg_term_test_A.agent != AttackerStrand.agent
    mesg_term_test_B.agent != AttackerStrand.agent
    mesg_term_test_A.agent != mesg_term_test_B.agent

    mesg_term_test_B.mesg_term_test_B_m in Ciphertext
} for 
    exactly 4 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 2 text,exactly 2 Ciphertext,
    exactly 1 mesg_term_test_A,exactly 1 mesg_term_test_B,
    4 Int
for {next is linear}