#lang forge

open "ootway_rees.rkt"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

option run_sterling "../documentation/temp_vis.js"
//option solver Glucose /*This doesn't seem to be working*/
option solver MiniSatProver
//option solver MiniSat /*This doesn't seem to be working*/

ootway_ress_base_test: run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S

    constrain_skeleton_ootway_rees_0

    //appropiate nonce and agent constraints
    //Nonces being different
    //only setting not equal for the places where the nonces are
    //generated seems more reliastic and less number of constraints

    //A generates m,na

    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_m

    //S generates nb (also can read na nb)
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_nb
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_m
    ootway_rees_S.ootway_rees_S_nb != ootway_rees_S.ootway_rees_S_m

    //These constraints similar to two_nonce also seems critical here
    /*
    ootway_rees_A.agent != AttackerStrand.agent
    ootway_rees_B.agent != AttackerStrand.agent 
    ootway_rees_S.agent != AttackerStrand.agent
    */
    /*
    ootway_rees_A.agent != ootway_rees_B.agent
    ootway_rees_B.agent != ootway_rees_S.agent
    ootway_rees_S.agent != ootway_rees_A.agent
    */
}for 
//why exactly needed here
//just increased size of message and started working have to 
//ask about that itself
//16 Timeslot should be enough trying larger number to check something
//mesg = Key + name + Ciphertext + texta
//mesg = 10 + 6 + 10 + 10
//Trying to ensure agent != Attacker not working
//some constraint is still wrong maybe unable to identify
    exactly 8 Timeslot,36 mesg,
    //number cof keys only long term so 4C2 so 6 should be enough?
    exactly 1 KeyPairs,exactly 10 Key,exactly 0 akey,exactly 10 skey,
    exactly 0 PrivateKey, exactly 0 PublicKey,

    //seems like 6 CipherText required and 3 text for na,nb,m
    exactly 4 name,exactly 10 text,exactly 10 Ciphertext,
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S,
    1 Int 
for {next is linear}
//look at learned_times for _B0 along with A_0 and attacker strand
//also check CipherText generated at time0
//write expression to find all names who have learnt a term (specifically key)
