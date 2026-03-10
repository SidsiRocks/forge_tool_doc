
option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

-- option solver MiniSatProver
-- option logtranslation 2
-- option coregranularity 1
-- option engine_verbosity 3
-- option core_minimization rce


pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

pred gen_honest_run{
    no (ccit_x_509_A.agent & ccit_x_509_B.agent)
}
pred originates_name[n:name,d:mesg]{
    some aStrand: (agent.n) | {
        originates[aStrand,d]
    }
}
-- TODO can add support for specifying this in defprotocol as a protocol level constraint clause perhaps
pred protocol_constr{
    all arbit_A : ccit_x_509_A | {
        arbit_A.ccit_x_509_A_b != Attacker => not corrected_attacker_learns[arbit_A.ccit_x_509_A_Ya]
        originates_name[arbit_A.ccit_x_509_A_b,arbit_A.ccit_x_509_A_Xb]
        originates_name[arbit_A.ccit_x_509_A_b,arbit_A.ccit_x_509_A_Yb]
    }
    all arbit_B : ccit_x_509_B | {
        arbit_B.ccit_x_509_B_a != Attacker => not corrected_attacker_learns[arbit_B.ccit_x_509_B_Yb]

        originates_name[arbit_B.ccit_x_509_B_a,arbit_B.ccit_x_509_B_Xa]
        originates_name[arbit_B.ccit_x_509_B_a,arbit_B.ccit_x_509_B_Ya]
    }
}

ccit_x_509_run : run {
    wellformed
    exec_ccit_x_509_A
    exec_ccit_x_509_B

    gen_honest_run
    not protocol_constr
}for
    exactly 4 Int
    for{
        next is linear
        honest_run_test
    }
