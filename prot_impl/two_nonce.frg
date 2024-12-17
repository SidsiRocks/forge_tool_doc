#lang forge 

open "two_nonce.rkt"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}
/*
option run_sterling "../documentation/temp_vis.js"
option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option engine_verbosity 3
option core_minimization rce
*/
two_nonce_init_pov : run {
    wellformed

    exec_two_nonce_init
    exec_two_nonce_resp

    constrain_skeleton_two_nonce_0
    
    two_nonce_resp.agent != two_nonce_init.agent
    //should not need restriction on a and b this time?

    //this may prevent attack have to check
    two_nonce_init.agent != AttackerStrand.agent
    two_nonce_resp.agent != AttackerStrand.agent

    //prevents responder from sending same nonce again
    two_nonce_resp.two_nonce_resp_n1 != two_nonce_resp.two_nonce_resp_n2
    //prevents attacker from sending duplicate n1,n2 in a run of protocol
    two_nonce_init.two_nonce_init_n1 != two_nonce_init.two_nonce_init_n2
    
    //attacker_learns[AttackerStrand,two_nonce_resp.two_nonce_resp_n2]
    
    //finding attack where init beleives it is talking to resp 
    //but attacker knows the nonce
    two_nonce_init.two_nonce_init_b = two_nonce_resp.agent
    corrected_attacker_learns[two_nonce_init.two_nonce_init_n2]
    //same nonce problem seems to be resolved
    //have to deal with initiator trying tot talk to attacker, may want to change that
    //when planning to detect an attack
    two_nonce_init.agent = AttackerStrand.agent
}for 
    exactly 6 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
    1 Int
for {next is linear}