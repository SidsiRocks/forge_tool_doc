#lang forge/domains/crypto

(defprotocol kao_chow_v1 basic
    (defrole init
        (vars (a b s name) (Kab skey) (Na Nb text))
        (trace
            (send (cat a b Na))
            ; (recv (cat 
            ;     (enc a b Na Kab (ltk a s)) 
            ;     (enc Na Kab) 
            ;     Nb
            ; ))
            ; (send (enc Nb Kab))
        )
        (constraint
            (non-orig (ltk a s))
            (uniq-orig Na) 
            (fresh-gen Na)
            ; (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kab skey) (Na Nb text))
        (trace 
            (recv (cat a b Na))
            (send (cat
                (enc a b Na Kab (ltk a s))
                (enc a b Na Kab (ltk b s))
            ))
        )
        (constraint
            (non-orig (ltk a s))
            (non-orig (ltk b s))
            ; (uniq-orig Kab) (fresh-gen Kab)
            ; (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Kab skey) (Na Nb text))
        (trace
            (recv (cat
                (enc a b Na Kab (ltk a s))
                (enc a b Na Kab (ltk b s))
            ))
            ; (send (cat 
            ;     (enc a b Na Kab (ltk a s)) 
            ;     (enc Na Kab) 
            ;     Nb
            ; ))
            ; (recv (enc Nb Kab))
        )
        (constraint
            (non-orig (ltk b s))
            ; (uniq-orig Nb)
            ; (fresh-gen Nb)
            ; (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton kao_chow_v1
    (vars (a b s name) (Kab skey) (Na Nb text))
    (defstrand init 1 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand resp 1 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
)

(defaltinstance honest_run_bounds 
    (Timeslot 4)
    (mesg 37)
    (Key 6) (name 4) (Ciphertext 10) (text 2) (tuple 15) (Hashed 0)
    (skey 6) (Attacker 1)
    (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 6)
    (init 1) (server 1) (resp 1)
    (have-ltks)
)