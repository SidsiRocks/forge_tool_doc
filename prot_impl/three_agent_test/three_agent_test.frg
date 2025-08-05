#lang forge

open "three_agent_test.rkt"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

three_agent_base_test : run {
    wellformed 
    exec_three_agent_A
    exec_three_agent_B
    exec_three_agent_S

    //constrain_skeleton_three_agent_0
}for 
    exactly 6 Timeslot,50 mesg,
    exactly 1 KeyPairs,exactly 8 Key,exactly 8 akey,0 skey,
    exactly 4 PrivateKey,exactly 4 PublicKey,

    exactly 4 name,exactly 6 text,exactly 20 Ciphertext,
    exactly 1 three_agent_A,exactly 1 three_agent_B,exactly 1 three_agent_S,
    1 Int
for {next is linear}