option run_sterling "../../crypto_viz_seq.js"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

--option solver MiniSatProver
--option logtranslation 2
--option coregranularity 1
--option engine_verbosity 3
--option core_minimization rce

--option solver "./run_z3.sh"

two_nonce_init_pov : run {
    wellformed

    exec_two_nonce_init
    exec_two_nonce_resp

    constrain_skeleton_two_nonce_0

    -- no (two_nonce_resp.agent & two_nonce_init.agent)
    --should not need restriction on a and b this time?

    --this may prevent attack have to check
    -- two_nonce_init.agent != AttackerStrand.agent
    -- two_nonce_resp.agent != AttackerStrand.agent
    -- not (Attacker in (two_nonce_init + two_nonce_resp).agent)
    --prevents responder from sending same nonce again
    -- two_nonce_resp.two_nonce_resp_n1 != two_nonce_resp.two_nonce_resp_n2
    --prevents attacker from sending duplicate n1,n2 in a run of protocol
    -- two_nonce_init.two_nonce_init_n1 != two_nonce_init.two_nonce_init_n2

    --attacker_learns[AttackerStrand,two_nonce_resp.two_nonce_resp_n2]

    --finding attack where init beleives it is talking to resp
    --but attacker knows the nonce
    -- two_nonce_init.two_nonce_init_b = two_nonce_resp.agent
    -- not (Attacker in two_nonce_init.two_nonce_init_b)
    -- corrected_attacker_learns[two_nonce_init.two_nonce_init_n2]
    --same nonce problem seems to be resolved
    --have to deal with initiator trying tot talk to attacker, may want to change that
    --when planning to detect an attack
}for
--    exactly 6 Timeslot,exactly 25 mesg,exactly 25 text,
--    exactly 25 atomic,exactly 6 nonce,
--    exactly 1 KeyPairs,exactly 6 Key,
--    exactly 6 akey,0 skey,
--    exactly 3 PrivateKey,exactly 3 PublicKey,
--    exactly 3 name,exactly 10 Ciphertext,
--    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
--    4 Int

--    exactly 6 Timeslot,exactly 25 mesg,exactly 6 Key,
--    exactly 6 akey,exactly 3 PublicKey,exactly 3 PrivateKey,
--    exactly 3 name,exactly 6 Ciphertext,exactly 2 text,exactly 8 tuple,
--    exactly 1 KeyPairs,
--    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
--    3 Int

--    exactly 6 Timeslot,25 mesg,
--    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
--    exactly 3 PrivateKey,exactly 3 PublicKey,
--    exactly 0 Hashed,
--    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
--    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
--    4 Int

--    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
--    3 Int
--    for{
--        next is linear
--        single_session
--    }

--    exactly 12 Timeslot,29 mesg,
--    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
--    exactly 3 PrivateKey,exactly 3 PublicKey,
--    exactly 0 Hashed,
--    exactly 3 name,exactly 10 text,exactly 10 Ciphertext,
--    exactly 2 two_nonce_init,exactly 2 two_nonce_resp,
--    3 Int
--for {next is linear}

--    exactly 2 two_nonce_init,exactly 2 two_nonce_resp,
--    3 Int
--    for{
--        next is linear
--        two_sessions
--    }

    exactly 3 Int
    for{
        next is linear
        alt_single_session
    }
--run {} for 3
