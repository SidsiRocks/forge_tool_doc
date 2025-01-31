#lang forge
open "ootway_step_0.rkt"
option run_sterling "../../crypto_viz.js"

pred prot_conditions{
    ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent

    //nothing to state nonces being different 
    //only one nonce being sent currently  

    ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
}

ootway_prot_run : run {
    wellformed
    prot_conditions
    exec_ootway_rees_A
    exec_ootway_rees_B
    constrain_skeleton_ootway_rees_0
}for 
    //mesg = Key + name + Ciphertext + text 
    //mesg = 1 (only one ltk)  + 3 (2 agent 1 attacker)+ 1 (only 1 enc term)+ 2 (m,na)
    exactly 4 Timeslot,7 mesg,
    exactly 1 KeyPairs,exactly 1 Key,exactly 0 akey,exactly 1 skey, //3 keys for ltk a s, ltk b s,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 3 name,exactly 2 text,exactly 1 Ciphertext, //4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate ; 4 Ciphertext should also work
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    1 Int