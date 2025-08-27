option run_sterling "../../crypto_viz_text_seq.js"
-- option verbose 10
-- option solver "../../../../../../../../../usr/bin/minisat"
option engine_verbosity 3

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}
pred A_nonce_cannot_be_regen {
    all type_flaw_prot_A_strand : type_flaw_prot_A | {
        all aStrand : strand | {
            generates[aStrand,type_flaw_prot_A_strand.type_flaw_prot_A_n] => (aStrand = type_flaw_prot_A_strand)
        }
    }
}
pred priv_key_not_in_gen {
    all k : PrivateKey | {
        not (k in (name.generated_times).Timeslot)
    }
}

type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B
    A_nonce_cannot_be_regen
    priv_key_not_in_gen

    type_flaw_prot_A.agent != AttackerStrand.agent
    type_flaw_prot_A.type_flaw_prot_A_b != AttackerStrand.agent
    corrected_attacker_learns[type_flaw_prot_A.type_flaw_prot_A_n]
    -- type_flaw_prot_B.agent != AttackerStrand.agent

    --below constraints to try and generate honest run first
    -- type_flaw_prot_A.type_flaw_prot_A_a = type_flaw_prot_A.agent
    -- type_flaw_prot_A.type_flaw_prot_A_b = type_flaw_prot_B.agent

    -- type_flaw_prot_B.type_flaw_prot_B_a = type_flaw_prot_A.agent
    -- type_flaw_prot_B.type_flaw_prot_B_b = type_flaw_prot_B.agent

    -- type_flaw_prot_A.agent != type_flaw_prot_B.agent
}for
    exactly 6 Timeslot,17 mesg,17 text,16 atomic,1 seq,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 6 Ciphertext,exactly 1 nonce,
    exactly 1 type_flaw_prot_A,exactly 2 type_flaw_prot_B,
    4 Int
for {next is linear}
