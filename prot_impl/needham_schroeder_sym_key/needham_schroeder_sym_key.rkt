#lang forge/domains/crypto

(defprotocol needham_schroeder_sym_key basic
    (defrole init 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace 
            (send (cat a b Na))
            (recv (enc (cat Na b Kab (enc (cat Kab a) (ltk b s))) (ltk a s)))
            (send (enc (cat Kab a) (ltk b s)))
            (recv (enc Nb Kab))
            (send (enc (hash Nb) Kab))
        )
        (constraint
            (non-orig (privk a))
            (non-orig Na) 
            (fresh-gen Na)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace
            (recv (cat a b Na))
            (send (enc (cat Na b Kab (enc (cat Kab a) (ltk b s))) (ltk a s)))
        )
        (constraint
            (non-orig (privk s))
            (uniq-orig Kab)
            (fresh-gen Kab)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace
            (recv (enc (cat Kab a) (ltk b s)))
            (send (enc Nb Kab))
            (recv (enc (hash Nb) Kab))
        )
        (constraint
            (uniq-orig Nb) (fresh-gen Nb)
            (non-orig (privk b))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton needham_schroeder_sym_key
    (vars (a b s name) (Na Nb text) (Kab skey))
    (defstrand init 5 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Na Na))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab) (Nb Nb))
)

(defaltinstance honest_run_bounds 
    (Timeslot 10)
    (mesg 43)
    (Key 11) (name 4) (Ciphertext 10) (text 8) (tuple 8) (Hashed 2)
    (akey 8) (skey 3) (Attacker 1)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1)
)