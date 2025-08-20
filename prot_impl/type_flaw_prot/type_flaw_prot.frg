option run_sterling "../../crypto_viz_text_seq.js"

type_flaw_prot_run : run {
    wellformed
    exec_type_flaw_prot_A
    exec_type_flaw_prot_B

    type_flaw_prot_A.agent != AttackerStrand.agent
    type_flaw_prot_B.agent != AttackerStrand.agent

    --below constraints to try and generate honest run first
    type_flaw_prot_A.type_flaw_prot_A_a = type_flaw_prot_A.agent
    type_flaw_prot_A.type_flaw_prot_A_b = type_flaw_prot_B.agent

    type_flaw_prot_B.type_flaw_prot_B_a = type_flaw_prot_A.agent
    type_flaw_prot_B.type_flaw_prot_B_b = type_flaw_prot_B.agent

}for 
    exactly 4 Timeslot,17 mesg,17 text,17 atomic,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,
    exactly 0 skey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 5 Ciphertext,exactly 3 nonce,
    exactly 1 type_flaw_prot_A,exactly 1 type_flaw_prot_B,
    4 Int
for {next is linear}
