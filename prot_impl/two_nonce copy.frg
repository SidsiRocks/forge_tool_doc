#lang forge 
open "two_nonce.rkt"
pred corrected_attacker_learns[d:mesg]{ d in Attacker.learned_times.Timeslot }
two_nonce_init_pov : run {
    wellformed

    exec_two_nonce_init
    exec_two_nonce_resp

    constrain_skeleton_two_nonce_0
    
    two_nonce_resp.agent != two_nonce_init.agent
    two_nonce_init.agent != AttackerStrand.agent
    two_nonce_resp.agent != AttackerStrand.agent
    two_nonce_resp.two_nonce_resp_n1 != two_nonce_resp.two_nonce_resp_n2
    two_nonce_init.two_nonce_init_n1 != two_nonce_init.two_nonce_init_n2
    two_nonce_init.two_nonce_init_b = two_nonce_resp.agent
    corrected_attacker_learns[two_nonce_init.two_nonce_init_n2]
}for 
    exactly 6 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
    1 Int
for {next is linear}