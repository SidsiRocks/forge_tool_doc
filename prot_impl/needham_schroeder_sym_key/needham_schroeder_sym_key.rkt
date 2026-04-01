#lang forge/domains/crypto

(defprotocol needham_schroeder_sym_key basic
    (defrole init 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace 
            (send (cat a b Na))
            (recv (enc (cat Na b Kab (enc (cat Kab a) (ltk b s))) (ltk a s)))
            (send (enc (cat Kab a) (ltk b s)))
            (recv (enc (cat Nb) Kab))
            (send (enc (cat (hash Nb)) Kab))
        )
        (constraint
            (non-orig (ltk a s))
            (uniq-orig Na) 
            (fresh-gen Na)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server 
        (vars (a b s name) (Na text) (Kab skey))
        (trace
            (recv (cat a b Na))
            (send (enc (cat Na b Kab (enc (cat Kab a) (ltk b s))) (ltk a s)))
        )
        (constraint
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            (uniq-orig Kab)
            (fresh-gen Kab)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Nb text) (Kab skey))
        (trace
            (recv (enc (cat Kab a) (ltk b s)))
            (send (enc (cat Nb) Kab))
            (recv (enc (cat (hash Nb)) Kab))
        )
        (constraint
            (uniq-orig Nb) (fresh-gen Nb)
            (non-orig (ltk b s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton needham_schroeder_sym_key
    (vars (a b s name) (Na text) (Kab skey))
    (defstrand init 5 (a a) (b b) (s s) (Kab Kab) (Na Na))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Na Na))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab))
)

(defaltinstance honest_run_bounds 
    (Timeslot 10)
    (mesg 45)
    (Key 3) (name 4) (Ciphertext 10) (text 8) (tuple 18) (Hashed 2)
    (skey 3) (Attacker 1)
    (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1)
)

(defaltinstance honest_run_bounds2
    (Timeslot 10)
    (mesg 59)

    (name 5)

    (Key 4) (skey 4)

    (Ciphertext 12)
    (tuple 25)
    (text 10)
    (Hashed 3)

    (enc-depth 3)
    (tuple-length 5)

    (init 1) (server 1) (resp 1)

    (Attacker 1)
    (akey 0)
    (PublicKey 0) (PrivateKey 0)
)