#lang forge/domains/crypto

(defprotocol yahalom_ban basic
    (defrole init 
        (vars (a b s name) (Na Nb text) (Kab skey) (msg mesg))
        (trace 
            (send (cat a Na))
            (recv (cat Nb (enc b Kab Na (ltk a s)) msg))
            (send (cat msg (enc Nb Kab)))
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
            (recv (cat b Nb (enc a Na (ltk b s))))
            (send (cat Nb (enc b Kab Na (ltk a s)) (enc a Kab Nb (ltk b s))))
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
            (send (cat b Nb (enc a Na (ltk b s))))
            (recv (cat (enc a Kab Nb (ltk b s)) (enc Nb Kab)))
        )
        (constraint 
            (non-orig (ltk b s))
            (uniq-orig Nb) (fresh-gen Nb)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton yahalom_ban
    (vars (a b s name) (Na Nb text) (Kab skey))
    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
)

(defskeleton attack 
    (vars (a b s name) (Na Nb text) (Kab skey))
    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand init 2 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 1 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 1 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb Nb))
)

(defaltinstance honest_run_bounds
    (Timeslot 8)
    (mesg 27)
    (Key 7) (name 4) (Ciphertext 5) (text 2) (tuple 9) (Hashed 0)
    (skey 7) (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 4)
    (init 1) (server 1) (resp 1) (Attacker 1)
    (have-ltks)
)

(defaltinstance attack_bounds 
    (Timeslot 7)
    (mesg 37)
    (Key 7) (name 4) (Ciphertext 8) (text 3) (tuple 15) (Hashed 0)
    (skey 7) (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 4)
    (init 2) (server 2) (resp 1) (Attacker 1)
    (have-ltks)
)