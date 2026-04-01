#lang forge/domains/crypto

(defprotocol denning_saco basic
    (defrole init
        (vars (a b s name) (Kab skey) (T text))
        (trace
            (send (cat a b))
            (recv (enc (cat b Kab T (enc (cat Kab a T) (ltk b s))) (ltk a s)))
            (send (enc (cat Kab a T) (ltk b s)))
        )
        (constraint
            (non-orig (privk a))
            (non-orig (ltk a s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kab skey) (T text))
        (trace
            (recv (cat a b))
            (send (enc (cat b Kab T (enc (cat Kab a T) (ltk b s))) (ltk a s)))
        )
        (constraint
            (non-orig (privk s))
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            (uniq-orig Kab)
            (fresh-gen Kab)
            (uniq-orig T)
            (fresh-gen T)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp
        (vars (a b s name) (Kab skey) (T text))
        (trace
            (recv (enc (cat Kab a T) (ltk b s)))
        )
        (constraint
            (non-orig (privk b))
            (non-orig (ltk b s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton denning_saco
    (vars (a b s name) (Kab skey) (T text))
    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand resp 1 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand resp 1 (a a) (b b) (s s) (Kab Kab) (T T))
)

(defaltinstance honest_run_bounds
    (Timeslot 6)
    (mesg 35)
    (Key 11) (name 4) (Ciphertext 6) (text 6) (tuple 8) (Hashed 0) 
    (akey 8) (skey 3) (Attacker 1)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1)
)

(defaltinstance attack_bounds
    (Timeslot 16)
    (mesg 35)
    (Key 11) (name 4) (Ciphertext 6) (text 6) (tuple 8) (Hashed 0) 
    (akey 8) (skey 3) (Attacker 1)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 2)
)