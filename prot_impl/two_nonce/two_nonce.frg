option run_sterling "../../crypto_viz_tuple.js"

pred corrected_attacker_learns[d:mesg]{
    d in (Attacker.learned_times).Timeslot
}

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

--option engine_verbosity 3
--option solver "./run_z3.sh"

pred depth_limitation{
  let subterm_rel = {msg1:mesg,msg2:mesg | {msg2 in (elems[msg1.components] + msg1.plaintext)}} | {
      no subterm_rel.subterm_rel.subterm_rel.subterm_rel.subterm_rel.subterm_rel
  }
}

two_nonce_init_pov : run {
    wellformed

    exec_two_nonce_init
    exec_two_nonce_resp

    constrain_skeleton_two_nonce_0

    two_nonce_init.agent != Attacker
    two_nonce_resp.agent != Attacker

    two_nonce_init.agent != two_nonce_resp.agent

    -- Attacker learns n2 when init believes they are not talking to attacker
    -- corrected_attacker_learns[two_nonce_init.two_nonce_init_n2]
    -- two_nonce_init.two_nonce_init_n2 != two_nonce_resp.two_nonce_resp_n2
    -- depth_limitation
}for
    exactly 6 Timeslot,exactly 25 mesg,exactly 6 Key,
    exactly 6 akey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 6 Ciphertext,exactly 2 text,exactly 8 tuple,
    exactly 1 KeyPairs,
    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
    3 Int
for {next is linear}

--run {} for 3
