#lang forge

open "ootway_rees.rkt"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

ootway_ress_base_test: run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S

    constrain_skeleton_ootway_rees_0

    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_nb
    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_m
    ootway_rees_A.ootway_rees_A_m  != ootway_rees_A.ootway_rees_A_nb
    ootway_rees_A.ootway_rees_A_a  != ootway_rees_A.ootway_rees_A_b
    ootway_rees_A.ootway_rees_A_a  != ootway_rees_A.ootway_rees_A_s
    ootway_rees_A.ootway_rees_A_s  != ootway_rees_A.ootway_rees_A_b

    
    ootway_rees_B.ootway_rees_B_na != ootway_rees_B.ootway_rees_B_nb
    ootway_rees_B.ootway_rees_B_na != ootway_rees_B.ootway_rees_B_m
    ootway_rees_B.ootway_rees_B_m  != ootway_rees_B.ootway_rees_B_nb
    ootway_rees_B.ootway_rees_B_a  != ootway_rees_B.ootway_rees_B_b
    ootway_rees_B.ootway_rees_B_a  != ootway_rees_B.ootway_rees_B_s
    ootway_rees_B.ootway_rees_B_s  != ootway_rees_B.ootway_rees_B_b

    
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_nb
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_m
    ootway_rees_S.ootway_rees_S_m  != ootway_rees_S.ootway_rees_S_nb
    ootway_rees_S.ootway_rees_S_a  != ootway_rees_S.ootway_rees_S_b
    ootway_rees_S.ootway_rees_S_a  != ootway_rees_S.ootway_rees_S_s
    ootway_rees_S.ootway_rees_S_s  != ootway_rees_S.ootway_rees_S_b

}for 
//why exactly needed here
//just increased size of message and started working have to 
//ask about that itself
//16 Timeslot should be enough trying larger number to check something

    exactly 8 Timeslot,50 mesg,
    exactly 1 KeyPairs,exactly 8 Key,exactly 0 akey,exactly 8 skey,
    exactly 0 PrivateKey, exactly 0 PublicKey,

    exactly 4 name,exactly 15 text,exactly 15 Ciphertext,
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S,
    1 Int 
for {next is linear}