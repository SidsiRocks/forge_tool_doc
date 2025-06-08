#lang forge
open "reorder_terms.rkt"

option run_sterling "../../crypto_viz.js"

reorder_terms_exmpl : run {
    wellformed 

    exec_reorder_terms_A
    exec_reorder_terms_B

    reorder_terms_A.agent != AttackerStrand.agent
    reorder_terms_B.agent != AttackerStrand.agent 
    reorder_terms_A.reorder_terms_A_n1 != reorder_terms_A.reorder_terms_A_n2
    reorder_terms_B.reorder_terms_B_n1 != reorder_terms_B.reorder_terms_B_n2
}for 
    exactly 4 Timeslot,15 mesg,
    exactly 1 KeyPairs,exactly 0 Key,exactly 0 akey,exactly 0 skey,
    exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 3 name,exactly 8 text,exactly 0 Ciphertext,
    exactly 1 reorder_terms_A,exactly 1 reorder_terms_B,
    4 Int
for{next is linear}
