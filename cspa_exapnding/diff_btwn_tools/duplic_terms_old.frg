#lang forge
open "duplic_terms.rkt"
option run_sterling "../../crypto_viz.js"

duplic_terms_exmpl : run {
    wellformed 

    exec_duplic_terms_A
    exec_duplic_terms_B 

    duplic_terms_A.agent != AttackerStrand.agent
    duplic_terms_B.agent != AttackerStrand.agent
}for 
    exactly 4 Timeslot,10 mesg,
    exactly 1 KeyPairs,exactly 0 Key,exactly 0 akey,exactly 0 skey,
    exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 3 name,exactly 5 text,exactly 0 Ciphertext,
    exactly 1 duplic_terms_A,exactly 1 duplic_terms_B,
    4 Int
for {next is linear}