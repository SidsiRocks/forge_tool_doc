#lang forge/domains/crypto

(defprotocol lowe_denning_saco basic
    (defrole init
        (vars (a b s name) (Kab skey) (T Nb text) (msg mesg))
        (trace
            (send (cat a b))
            (recv (enc b Kab T msg (ltk a s)))
            (send msg)
            (recv (enc Nb Kab))
            (send (enc (hash Nb) Kab))
        )
        (constraint
            (non-orig (ltk a s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kab skey) (T text))
        (trace
            (recv (cat a b))
            (send (enc b Kab T (enc Kab a T (ltk b s)) (ltk a s)))
        )
        (constraint
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            (uniq-orig Kab) (fresh-gen Kab)
            (uniq-orig T) (fresh-gen T)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp
        (vars (a b s name) (Kab skey) (T Nb text))
        (trace
            (recv (enc Kab a T (ltk b s)))
            (send (enc Nb Kab))
            (recv (enc (hash Nb) Kab))
        )
        (constraint
            (non-orig (ltk b s))
            (uniq-orig Nb) (fresh-gen Nb)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton lowe_denning_saco
    (vars (a b s name) (Kab skey) (T Nb text) (msg mesg) (init role_init) (server role_server) (resp role_resp))
    (defstrand init 5 (a a) (b b) (s s) (Kab Kab) (T T) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab) (T T) (Nb Nb))

    (deftrace honest_run
        (send-from init (cat a b))
        (recv-by server (cat a b))

        (send-from server (enc b Kab T (enc Kab a T (ltk b s)) (ltk a s)))
        (recv-by init (enc b Kab T msg (ltk a s)))

        (send-from init msg)
        (recv-by resp (enc Kab a T (ltk b s)))

        (send-from resp (enc Nb Kab))
        (recv-by init (enc Nb Kab))

        (send-from init (enc (hash Nb) Kab))
        (recv-by resp (enc (hash Nb) Kab))
    )
)

(defaltinstance honest_run_bounds
    (Timeslot 10)
    (mesg 26)
    (Key 7) (name 4) (Ciphertext 6) (text 2) (tuple 6) (Hashed 1) 
    (akey 0) (skey 7) (Attacker 1)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1)
    (have-ltks)
)