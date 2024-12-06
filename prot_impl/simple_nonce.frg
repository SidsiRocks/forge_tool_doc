#lang forge

open "simple_nonce.rkt"

simple_nonce_init_pov: run {
    wellformed
    
    exec_simple_nonce_init
    exec_simple_nonce_resp

    constrain_skeleton_simple_nonce_0
    simple_nonce_resp.agent != simple_nonce_init.agent

    //might not need name restriction since would be 
    //need to decrypt it hence need to have acess to the appropiate keys
    //will cross check   

    //seems like two agents getting assigned same name have to change that
    simple_nonce_init.simple_nonce_init_a = simple_nonce_init.agent
    simple_nonce_resp.simple_nonce_resp_b = simple_nonce_resp.agent

    //added this so that no communication with themselves again as a,b could be same
    simple_nonce_init.simple_nonce_init_a != simple_nonce_init.simple_nonce_init_b
    simple_nonce_resp.simple_nonce_resp_b != simple_nonce_resp.simple_nonce_resp_a

    simple_nonce_init.agent != AttackerStrand.agent
    simple_nonce_resp.agent != AttackerStrand.agent
}for 
//now needs exact bound for mesg?
    exactly 4 Timeslot,25 mesg,
    exactly 1 KeyPairs, exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    //setting larger bound for text seems to lead to 
    //multiple duplicate cases with just the nonce used being changed
    exactly 3 name,exactly 5 text,exactly 10 Ciphertext,
    exactly 1 simple_nonce_init,exactly 1 simple_nonce_resp,
    1 Int

for {next is linear}