#lang forge

open "simple_enc.rkt"

simple_enc_responder_pov: run {
    wellformed

    exec_simple_enc_init
    exec_simple_enc_resp

    simple_enc_resp.agent != simple_enc_init.agent

    simple_enc_init.simple_enc_init_a = simple_enc_init.agent
    simple_enc_resp.simple_enc_resp_b = simple_enc_resp.agent
}for 
    exactly 4 Timeslot,20 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey, exactly 3 PublicKey,
    //it seems like if you mention exactly then bit-width 
    //of Int can be 1 (maybe no counting needed internally)
    //writing exactly makes it work though
    
    //also seem like if you do not mention exactly then 
    //the execution is not rendered properly
    exactly 3 name,0 text,exactly 4 Ciphertext,
    exactly 1 simple_enc_init,exactly 1 simple_enc_resp,
    1 Int
for {next is linear}