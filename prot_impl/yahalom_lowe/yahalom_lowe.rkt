#lang forge/domains/crypto

(defprotocol yahalom_lowe basic 
    (defrole init 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace 
            (send (cat a Na))
            (recv (enc b Kab Na Nb (ltk a s)))
            (send (enc a b s Nb Kab))
        )
        (constraint 
            (non-orig (ltk a s))
            (uniq-orig Na) (fresh-gen Na)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace 
            (recv (enc a Na Nb (ltk b s)))
            (send (enc b Kab Na Nb (ltk a s)))
            (send (enc a Kab (ltk b s)))
        )
        (constraint 
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            (fresh-gen Kab) (uniq-orig Kab)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Na Nb text) (Kab skey))
        (trace 
            (recv (cat a Na))
            (send (enc a Na Nb (ltk b s)))
            (recv (enc a Kab (ltk b s)))
            (recv (enc a b s Nb Kab))
        )
        (constraint 
            (non-orig (ltk b s))
            (uniq-orig Nb) (fresh-gen Nb)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton yahalom_lowe
    (vars (a b s name) (Na Nb text) (Kab skey))
    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 3 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand resp 4 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
)

(defaltinstance honest_run_bounds
    (Timeslot 10)
    (mesg 22)
    (Key 7) (name 4) (Ciphertext 4) (text 2) (tuple 5) (Hashed 0)
    (skey 7) (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1) (Attacker 1)
    (have-ltks)
)