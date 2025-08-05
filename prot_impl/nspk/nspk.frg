#lang forge

open "nspk.rkt"

option run_sterling "../vis/crypto_viz.js"

nspk_responder_pov: run {
    wellformed 
    
    exec_nspk_A
    exec_nspk_B
    exec_nspk_S

    constrain_skeleton_nspk_0

    nspk_A.agent != nspk_B.agent
    //keeping server also different for now don't think that should be an exact requirement
    nspk_A.agent != nspk_S.agent
    nspk_B.agent != nspk_S.agent
}for 
    //7 messages through attacker so 14 in total kept mesg bound high on purpose doesn't matter directly here
    exactly 14 Timeslot, 40 mesg,
    //8 keys for A,B,S,Attacker 1 Public and 1 Private each
    exactly 1 KeyPairs, exactly 8 Key, exactly 8 akey, exactly 0 skey,
    exactly 4 PrivateKey,exactly 4 PublicKey,

    //4 names for A,B,S,Attacker , text for nonces 2 should be enough kept 5 just in case
    //8 CipherText for encrypted expressions 5 in protocol kept 8 just in case
    exactly 4 name, 5 text, exactly 8 Ciphertext,
    //keeping 1 A,1 B and 1 S
    exactly 1 nspk_A, exactly 1 nspk_B, exactly 1 nspk_S,
    //1 bit width doesn't worj not exactly sure why 
    5 Int
for {next is linear}