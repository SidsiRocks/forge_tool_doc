#lang forge

open "lowe_ns.rkt"
pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}
/*
lowe_ns_init_pov: run {
    wellformed 
    exec_lowe_ns_init
    exec_lowe_ns_resp

    constrain_skeleton_lowe_ns_0

    lowe_ns_resp.agent != lowe_ns_init.agent

    --may not be needed anymore will check
    --why doesn't every strand have unique name
    --might want to check
    lowe_ns_init.agent != AttackerStrand.agent
    lowe_ns_resp.agent != AttackerStrand.agent

    --prevents sender from sending same nonce twice
    lowe_ns_resp.lowe_ns_resp_n1 != lowe_ns_resp.lowe_ns_resp_n2
    --prevents attacker from sending duplicate to init
    lowe_ns_init.lowe_ns_init_n1 != lowe_ns_init.lowe_ns_init_n2
}for 
    exactly 6 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
    exactly 1 lowe_ns_init,exactly 1 lowe_ns_resp,
    1 Int
for {next is linear}
*/

--firgure out how to run from command line to properly
--check this
lowe_ns_init_pov_check: check {
    (wellformed and
    exec_lowe_ns_init and
    exec_lowe_ns_resp and

    constrain_skeleton_lowe_ns_0 and

    lowe_ns_resp.agent != lowe_ns_init.agent and

    --may not be needed anymore will check
    --why doesn't every strand have unique name
    --might want to check
    lowe_ns_init.agent != AttackerStrand.agent and
    lowe_ns_resp.agent != AttackerStrand.agent and

    --prevents sender from sending same nonce twice
    lowe_ns_resp.lowe_ns_resp_n1 != lowe_ns_resp.lowe_ns_resp_n2 and
    --prevents attacker from sending duplicate to init
    lowe_ns_init.lowe_ns_init_n1 != lowe_ns_init.lowe_ns_init_n2 and


    lowe_ns_init.lowe_ns_init_b = lowe_ns_resp.agent ) implies
    not corrected_attacker_learns[lowe_ns_init.lowe_ns_init_n2]   
}for 
    exactly 6 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
    exactly 1 lowe_ns_init,exactly 1 lowe_ns_resp,
    1 Int
for {next is linear}