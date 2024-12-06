#lang forge
open "ns.rkt"
option run_sterling "../vis/crypto_viz.js"

ns_responder_pov: run{
    wellformed

    exec_ns_init
    exec_ns_resp
    constrain_skeleton_ns_0 //0 indexed i beleive

    ns_resp.agent != ns_init.agent
} for 
    exactly 6 Timeslot, 30 mesg, 
    exactly 1 KeyPairs, exactly 6 Key, exactly 6 akey, exactly 0 skey,
    exactly 3 PrivateKey, exactly 3 PublicKey,
    exactly 3 name,exactly 5 text, exactly 6 Ciphertext,
    exactly 1 ns_init, exactly 1 ns_resp,
    5 Int
for {next is linear}
