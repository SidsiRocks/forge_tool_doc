#lang forge 

open "simple.rkt"

option run_sterling "../vis/crypto_viz.js"

--seem to be working now, haven't added restriction on attacker to send own name so 
--
simple_responder_pov: run {
    wellformed 

    exec_simple_init
    exec_simple_resp

    --this prevents talking to itself
    simple_resp.agent != simple_init.agent

    --these ensure name a,b not same problems 
    --still doesn't ensure the name sent is their own
    --simple_resp.simple_resp_a != simple_resp.simple_resp_b
    --simple_init.simple_init_a != simple_init.simple_init_b

    --simple_resp.simple_resp_a = simple_init.simple_init_a
    simple_resp.simple_resp_b = simple_resp.agent
    simple_init.simple_init_a = simple_init.agent --assuming like .agent .name is also present
    --seems like init/resp getting same name as attacker
    --simple_resp.agent != AttackerStrand.agent
    --simple_init.agent != AttackerStrand.agent
} for 
    --seems like not all agents getting same name 
    exactly 4 Timeslot, 10 mesg,
    exactly 1 KeyPairs, exactly 0 Key,exactly 0 akey, 0 skey,
    exactly 0 PrivateKey, exactly 0 PublicKey,
    --need one name for attacker as well so 3 name not 2 name
    exactly 3 name, 0 text,exactly 0 Ciphertext,
    exactly 1 simple_init, exactly 1 simple_resp,
    1 Int
for {next is linear}
