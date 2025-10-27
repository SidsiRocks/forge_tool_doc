option run_sterling "../../crypto_viz_seq_hash.js"

pred uniq_orig[d:mesg]{
    one aStrand:strand | {
        originates[aStrand,d] or generates[aStrand,d]
    }
}
pred uniq_orig_strand[s:strand,d:mesg]{
    originates[s,d] or generates[s,d]
}
pred non_orig[d:mesg]{
    no aStrand:strand | {
        originates[aStrand,d] or generates[aStrand,d]
    }
}

andrew_rpc_term_test : run {
    wellformed
    exec_andrew_secure_rpc_A
    exec_andrew_secure_rpc_B
    constrain_skeleton_andrew_secure_rpc_0

    andrew_secure_rpc_A.agent != Attacker
    andrew_secure_rpc_B.agent != Attacker


    let a_name = andrew_secure_rpc_A.agent | {
    let b_name = andrew_secure_rpc_B.agent | {
        (one a_name) and (one b_name) and (a_name != b_name)
        all arbitrary_A_andrew_secure_rpc : andrew_secure_rpc_A | {
        let A0 = arbitrary_A_andrew_secure_rpc | {
        let na = andrew_secure_rpc_A_na | {
        let kab_ = andrew_secure_rpc_A_kab_ | {
            A0.andrew_secure_rpc_A_a = A0.agent
            -- next line constraint only for generating honest run
            A0.andrew_secure_rpc_A_b != Attacker

            uniq_orig_strand[A0,A0.na] and uniq_orig_strand[A0,A0.kab_]
            A0.kab_ != getLTK[a_name,b_name]
            not ( A0.na in andrew_secure_rpc_B.(andrew_secure_rpc_B_nb + andrew_secure_rpc_B_nb_)
 )        }}}}

        all arbitrary_B_andrew_secure_rpc : andrew_secure_rpc_B | {
        let B0 = arbitrary_B_andrew_secure_rpc | {
        let nb = andrew_secure_rpc_B_nb | {
        let nb_ = andrew_secure_rpc_B_nb_ | {
            B0.andrew_secure_rpc_B_b = B0.agent
            -- next line constraint only for generating honest run
            B0.andrew_secure_rpc_B_a != Attacker

            uniq_orig_strand[B0,B0.nb] and uniq_orig_strand[B0,B0.nb_]
            not ( B0.nb in andrew_secure_rpc_A.andrew_secure_rpc_A_na )
            not ( B0.nb_ in andrew_secure_rpc_A.andrew_secure_rpc_A_na )
        }}}}

        non_orig[getLTK[a_name,b_name]]
    }}

}for
    exactly 8 Timeslot,22 mesg,
    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,3 skey,
    exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 3 name,exactly 6 text,exactly 6 Ciphertext,
    exactly 1 andrew_secure_rpc_A,exactly 1 andrew_secure_rpc_B,
    3 Int
for {next is linear}
