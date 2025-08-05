#lang forge 

open "new_reorder_terms.rkt"

option run_sterling "../../../crypto_viz.js"


new_reorder_terms_pov : run {
    wellformed 

    exec_new_reorder_terms_A
    exec_new_reorder_terms_B

    new_reorder_terms_A.agent != new_reorder_terms_B.agent
    new_reorder_terms_A.agent != AttackerStrand.agent
    new_reorder_terms_B.agent != AttackerStrand.agent

    new_reorder_terms_A.new_reorder_terms_A_a = new_reorder_terms_A.agent
    new_reorder_terms_A.new_reorder_terms_A_b = new_reorder_terms_B.agent

    new_reorder_terms_B.new_reorder_terms_B_a = new_reorder_terms_A.agent
    new_reorder_terms_B.new_reorder_terms_B_b = new_reorder_terms_B.agent

    new_reorder_terms_A.new_reorder_terms_A_n1 != new_reorder_terms_A.new_reorder_terms_A_n2 
    new_reorder_terms_B.new_reorder_terms_B_n1 != new_reorder_terms_B.new_reorder_terms_B_n2 

    constrain_skeleton_new_reorder_terms_0
    constrain_skeleton_new_reorder_terms_1
}for 
    exactly 4 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,exactly 3 skey,
    exactly 0 PrivateKey,exactly 0 PublicKey,

    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
    exactly 1 new_reorder_terms_A,exactly 1 new_reorder_terms_B,
    5 Int
for {next is linear}