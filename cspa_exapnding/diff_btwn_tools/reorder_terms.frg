option run_sterling "../../crypto_viz_seq.js"

reorder_terms_exmpl : run {
    wellformed 

    exec_reorder_terms_A
    exec_reorder_terms_B

    reorder_terms_A.agent != AttackerStrand.agent
    reorder_terms_B.agent != AttackerStrand.agent 
}for 
    exactly 4 Timeslot,15 mesg,
    exactly 1 KeyPairs,exactly 0 Key,exactly 0 akey,exactly 0 skey,
    exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 3 name,exactly 8 text,exactly 0 Ciphertext,
    exactly 1 duplic_terms_A,exactly 1 duplic_terms_B,
    4 Int
for{next is linear}
