#lang forge/domains/crypto

(defprotocol needham_schroeder_sym_key basic
    (defrole init 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace 
            (send (cat a b Na))
            (recv (enc Na b Kab (enc Kab a (ltk b s)) (ltk a s)))
            ; (send (enc (cat Kab a) (ltk b s)))
            ; (recv (enc (cat Nb) Kab))
            ; (send (enc (cat (hash Nb)) Kab))
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
            (send (enc Na b Kab (enc Kab a (ltk b s)) (ltk a s)))
        )
        (constraint
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            (uniq-orig Kab)
            (fresh-gen Kab)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    ; (defrole resp 
    ;     (vars (a b s name) (Nb text) (Kab skey))
    ;     (trace
    ;         (recv (enc (cat Kab a) (ltk b s)))
    ;         (send (enc (cat Nb) Kab))
    ;         (recv (enc (cat (hash Nb)) Kab))
    ;     )
    ;     (constraint
    ;         (uniq-orig Nb) (fresh-gen Nb)
    ;         (non-orig (ltk b s))
    ;         (not-eq a b) (not-eq a s) (not-eq b s)
    ;     )
    ; )
)

(defskeleton needham_schroeder_sym_key
    (vars (a b s name) (Na text) (Kab skey))
    (defstrand init 2 (a a) (b b) (s s) (Kab Kab) (Na Na))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Na Na))
    ; (defstrand resp 3 (a a) (b b) (s s) (Kab Kab))
)

(defaltinstance honest_run_bounds 
    (Timeslot 4)
    (mesg 44)
    (Key 3) (name 3) (Ciphertext 10) (text 8) (tuple 18) (Hashed 2)
    (skey 3) (Attacker 1)
    (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 3) (tuple-length 5)
    (init 1) (server 1)
)