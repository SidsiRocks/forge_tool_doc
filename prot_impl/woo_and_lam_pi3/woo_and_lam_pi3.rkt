#lang forge/domains/crypto

(defprotocol woo_and_lam_pi3 basic 
    (defrole init 
        (vars (a b s name) (Nb text))
        (trace 
            (send a)
            (recv Nb)
            (send (enc Nb (ltk a s)))
        )
        (constraint 
            (non-orig (ltk a s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Nb text) (msg mesg))
        (trace 
            (recv a)
            (send Nb)
            (recv msg)
            (send (enc a msg (ltk b s)))
            (recv (enc a Nb (ltk b s)))
        )
        (constraint 
            (non-orig (ltk b s))
            (fresh-gen Nb) (uniq-orig Nb)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server 
        (vars (a b s name) (Nb text))
        (trace 
            (recv (enc a (enc Nb (ltk a s)) (ltk b s)))
            (send (enc a Nb (ltk b s)))
        )
        (constraint 
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton woo_and_lam_pi3
    (vars (a b s name) (Nb text) (init_strand role_init) (resp_strand role_resp) (server_strand role_server))
    (defstrand init 3 (a a) (b b) (s s) (Nb Nb))
    (defstrand resp 5 (a a) (b b) (s s) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Nb Nb))

    (deftrace honest_run
        (send-from init_strand a)
        (recv-by resp_strand a)
    )
)

(defaltinstance honest_run_bounds 
    (Timeslot 10)
    (mesg 21)
    (Key 6) (name 4) (Ciphertext 4) (text 1) (tuple 6) (Hashed 0)
    (skey 6) (akey 0)
    (PublicKey 0) (PrivateKey 0) 
    (enc-depth 2) (tuple-length 2)
    (init 1) (resp 1) (server 1) (Attacker 1)
    (have-ltks)
)