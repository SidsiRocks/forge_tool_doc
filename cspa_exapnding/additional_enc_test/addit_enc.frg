#lang forge
open "addit_enc.rkt"
option run_sterling "../../crypto_viz.js"
addit_enc_run : run {
    wellformed 
    exec_addit_enc_A
    exec_addit_enc_B
}
for 
    exactly 4 Timeslot,16 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 2 text,exactly 2 Ciphertext,
    exactly 1 addit_enc_A,exactly 1 addit_enc_B,
    1 Int
for {next is linear}    