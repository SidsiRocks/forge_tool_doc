option run_sterling "../../crypto_viz_seq.js"

//option run_sterling off
pred prot_conditions{
        
    //ensure agents performing their own role correctly
    
    ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    ootway_rees_A.ootway_rees_A_b = ootway_rees_B.agent
    ootway_rees_A.ootway_rees_A_s = ootway_rees_S.agent

    ootway_rees_B.ootway_rees_B_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent
    ootway_rees_B.ootway_rees_B_s = ootway_rees_S.agent
    
    ootway_rees_S.ootway_rees_S_a = ootway_rees_A.agent
    ootway_rees_S.ootway_rees_S_b = ootway_rees_B.agent
    ootway_rees_S.ootway_rees_S_s = ootway_rees_S.agent 
    

    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_m  
    
    ootway_rees_B.ootway_rees_B_nb != ootway_rees_B.ootway_rees_B_m 
    
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_kab
    ootway_rees_S.ootway_rees_S_nb != ootway_rees_S.ootway_rees_S_kab
    ootway_rees_S.ootway_rees_S_m  != ootway_rees_S.ootway_rees_S_kab
    //ensuring k_ab is not a long term key
    //no (KeyPairs.ltks).(ootway_rees_S.ootway_rees_S_kab)

    ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
    ootway_rees_S.agent != Attacker
    
    //Adding this below by itself makes it unsat somehow
    //ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_nb

    //Adding these to create an honest run of the protocol
    ootway_rees_A.ootway_rees_A_b = ootway_rees_B.agent 
    ootway_rees_A.ootway_rees_A_s = ootway_rees_S.agent 

    ootway_rees_B.ootway_rees_B_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_s = ootway_rees_S.agent

    ootway_rees_S.ootway_rees_S_a = ootway_rees_A.agent
    ootway_rees_S.ootway_rees_S_b = ootway_rees_B.agent

    //added this because a run generated code where ltk was sent instead of k_ab
    not (ootway_rees_S.ootway_rees_S_kab in (name.(name.(KeyPairs.ltks))))
}

new_ootway_prot_run : run {
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
    exec_ootway_rees_S
    constrain_skeleton_ootway_rees_0
} for 
    //mesg = Key + name + Ciphertext + text
    //mesg = 3   + 4    + 9          + 4
    exactly 8 Timeslot,20 mesg,
    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,exactly 3 skey, //3 keys for ltk a s, ltk b s,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 4 name,exactly 4 text,exactly 9 Ciphertext, //4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate ; 4 Ciphertext should also work
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S,
    4 Int
for {next is linear}