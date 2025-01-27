#lang forge
open "ootway_rees.rkt"
option run_sterling "../vis/crypto_viz.js"

pred prot_conditions{
    //ensure agents performing their own role correctly
    ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent
    ootway_rees_S.ootway_rees_S_s = ootway_rees_S.agent 

    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_m  
    
    ootway_rees_B.ootway_rees_B_nb != ootway_rees_B.ootway_rees_B_m 
    ootway_rees_B.ootway_rees_B_nb != ootway_rees_B.ootway_rees_B_na   
    
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_kab
    ootway_rees_S.ootway_rees_S_nb != ootway_rees_S.ootway_rees_S_kab
    ootway_rees_S.ootway_rees_S_m  != ootway_rees_S.ootway_rees_S_kab

    ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
    ootway_rees_S.agent != Attacker
}

ootway_prot_run : run {
    wellformed
    prot_conditions
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S
    constrain_skeleton_ootway_rees_0
} for 
    //mesg = Key + name + Ciphertext + text
    //mesg = 3   + 4    + 9          + 4
    exactly 8 Timeslot,20 mesg,
    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,exactly 3 skey, //3 keys for ltk a s, ltk b s,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 4 name,exactly 4 text,exactly 9 Ciphertext, //4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate 
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S,
    1 Int
for {next is linear}