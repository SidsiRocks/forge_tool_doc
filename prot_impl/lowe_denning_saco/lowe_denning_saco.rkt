#lang forge/domains/crypto

(defprotocol lowe_denning_saco basic
    (defrole init
        (vars (a b s name) (Kas Kbs Kab skey) (T Nb text))
        (trace
            (send (cat a b))
            (recv (enc (cat b Kab T (enc (cat Kab a T) Kbs)) Kas))
            (send (enc (cat Kab a T) Kbs))
            (recv (enc Nb Kab))
            (send (enc (hash Nb) Kab))
        )
        (constraint
            (non-orig (privk a))
            (non-orig Kas)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kas Kbs Kab skey) (T Nb text))
        (trace
            (recv (cat a b))
            (send (enc (cat b Kab T (enc (cat Kab a T) Kbs)) Kas))
        )
        (constraint
            (non-orig (privk s))
            (non-orig Kas)
            (non-orig Kbs)
            (uniq-orig Kab)
            (uniq-orig T)
            (fresh-gen T)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp
        (vars (a b s name) (Kas Kbs Kab skey) (T Nb text))
        (trace
            (recv (enc (cat Kab a T) Kbs))
            (send (enc Nb Kab))
            (recv (enc (hash Nb) Kab))
        )
        (constraint
            (uniq-orig Nb)
            (fresh-gen Nb)
            (non-orig (privk b))
            (non-orig Kbs)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton lowe_denning_saco
    (vars (a b s name) (Kas Kbs Kab skey) (T Nb text))
    (defstrand init 5 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (T T) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (T T) (Nb Nb))
    (defstrand resp 3 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (T T) (Nb Nb))
)

(defaltinstance honest_run_bounds
    (Timeslot 10)
    (mesg 45)
    (Key 11) (name 4) (Ciphertext 10) (text 10) (tuple 8) (Hashed 2) 
    (akey 8) (skey 3) (Attacker 1)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1)
)