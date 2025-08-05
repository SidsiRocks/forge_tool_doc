#lang forge 
open "enc_term.rkt"

option run_sterling "../../../crypto_viz.js"

enc_term_exmpl : run {
    wellformed
    
    exec_enc_term_A
    exec_enc_term_B
    
    constrain_skeleton_enc_term_0
}for 
    exactly 4 Timeslot,30 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,exactly 0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,
    exactly 3 name,exactly 10 text,exactly 8 Ciphertext,
    exactly 1 enc_term_A,exactly 1 enc_term_B,
    4 Int
for {next is linear}
