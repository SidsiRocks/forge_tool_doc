#lang forge
open "ootway_step_2.rkt"
option run_sterling "../../crypto_viz.js"
pred prot_conditions{
    ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent
    ootway_rees_S.ootway_rees_S_s = ootway_rees_S.agent

    ootway_rees_B.ootway_rees_B_na  != ootway_rees_B.ootway_rees_B_nb

    ootway_rees_S.ootway_rees_S_kab != ootway_rees_S.ootway_rees_S_na
    ootway_rees_S.ootway_rees_S_kab != ootway_rees_S.ootway_rees_S_nb
    //added this because generated a scenario where 
    //sent ltk instead of k_ab
    not (ootway_rees_S.ootway_rees_S_kab in (name.(name.(KeyPairs.ltks))))

    ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
    ootway_rees_S.agent != Attacker
}
ootway_prot_run : run {
    //should not ideally need this anyway
    all n: name | no getLTK[n,n]
    //placing constraint that no long term key can be generated
    //first part is all long term keys, second part is all generated terms
    //the set difference should be empty
    //no (  (name.(name.(KeyPairs.ltks))) - (name.generated_times.Timeslot))
    //Above was the old constraint which had incorrect logic

    //This is what the correct constraint would look like
    (name.(name.(KeyPairs.ltks))) = (name.(name.(KeyPairs.ltks))) - (name.generated_times.Timeslot)

    wellformed
    prot_conditions
    exec_ootway_rees_A
    exec_ootway_rees_B
    constrain_skeleton_ootway_rees_0
}for 
    //mesg = Key + name + Ciphertext + text 
    //mesg = 3 (two ltk,one k_ab)  + 4 (3 agent 1 attacker)+ 3 (only 3 enc term)+ 3 (m,na,nb)
    exactly 6 Timeslot,13 mesg,
    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,exactly 3 skey, //1 key for ltk a b,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 4 name,exactly 3 text,exactly 3 Ciphertext, //4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate ; 4 Ciphertext should also work
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,exactly 1 ootway_rees_S,
    1 Int
for {next is linear}