#lang forge
open "ootway_step_1.rkt"
option run_sterling "../../crypto_viz.js"
option solver MiniSatProver
option logtranslation 2
option coregranularity 1
option engine_verbosity 3
option core_minimization rce
//now the visualizer is broken in some way
pred prot_conditions{
    ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent

    //nothing to state nonces being different 
    //only one nonce being sent currently  

    ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
}
//the execution is almost correct with only 
//  ootway_rees_B.agent != Attacker
ootway_prot_run : run {
    wellformed
    prot_conditions
    exec_ootway_rees_A
    exec_ootway_rees_B
    constrain_skeleton_ootway_rees_0
}for 
    //mesg = Key + name + Ciphertext + text 
    //mesg = 2 (one ltk,one k_ab)  + 3 (2 agent 1 attacker)+ 2 (only 2 enc term)+ 2 (m,na)
    exactly 4 Timeslot,9 mesg,
    exactly 1 KeyPairs,exactly 2 Key,exactly 0 akey,exactly 2 skey, //1 key for ltk a b,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 3 name,exactly 2 text,exactly 2 Ciphertext, //4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate ; 4 Ciphertext should also work
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    1 Int
for {next is linear}