#lang forge

open "kao_chow.rkt"

option run_sterling "../vis/crypto_viz.js"

kao_chow_responder_pov : run {
    wellformed

    exec_kao_chow_A
    exec_kao_chow_B
    exec_kao_chow_S

    constrain_skeleton_kao_chow_0

    kao_chow_A.agent != kao_chow_B.agent 
    kao_chow_S.agent != kao_chow_A.agent 
    kao_chow_S.agent != kao_chow_B.agent 
// before was giving attacker one private key and
// one public, should give long term key here? else would
// not be able to intercat at all?
} for 
    exactly 8 Timeslot, 60 mesg,
    exactly 1 KeyPairs, exactly 6 Key,exactly 0 akey, exactly 6 skey,
    //here also 2 nonces might be enough but sending more
    exactly 4 name, 5 text, exactly 10 Ciphertext,
    exactly 1 kao_chow_A, exactly 1 kao_chow_B, exactly 1 kao_chow_S,
    //not clear wht larger int needed here
    5 Int
//why this needed separately
for {next is linear}