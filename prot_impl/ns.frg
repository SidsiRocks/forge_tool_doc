#lang forge

open "ns.rkt"

option run_sterling "../vis/crypto_viz.js"

/*
Where base.frg explicitly imported?
*/
ns_responder_pov: run{
    wellformed

    exec_ns_init
    exec_ns_resp
    constrain_skeleton_ns_0 //0 indexed i beleive

    ns_resp.agent != ns_init.agent
} for 
    exactly 6 Timeslot, 30 mesg, 
    //may want to reduce mesg bound later just kept high for now
    //we are using name instead of key could be causing problems
    exactly 1 KeyPairs, exactly 6 Key, exactly 6 akey, exactly 0 skey,
    exactly 3 PrivateKey, exactly 3 PublicKey,
    //should be atleast 2 text since 2 nonces keeping larger to see
    //may have to replace exactly with atleast

    //just noticed here text doesn't work need exact bound here as well
    //hesistant to keep text with an exact bound, however I think exact
    //bound need not mean each text is used in this context
    exactly 3 name,exactly 5 text, exactly 6 Ciphertext,
    exactly 1 ns_init, exactly 1 ns_resp,
    //not clear why need larger int here 1 Int is not working for some reason?
    //was working for reflect somehow
    5 Int
//apparently ensures Timeslot which contains this
//field will follow given bound exactly even if exactly 
//was not mentioned
//however we mentioned exactly so unclear how this works
for {next is linear}
