#lang forge/domains/crypto

(defprotocol needham_schroeder_sym_key basic
    (defrole init 
        (vars (a b s name) (Na Nb text) (Kab skey) (msg mesg))
        (trace 
            (send (cat a b Na))
            ; (recv (enc Na b Kab (enc Kab a (ltk b s)) (ltk a s))) ; actual message
            (recv (enc Na b Kab msg (ltk a s)))
            ; (send (enc Kab a (ltk b s)))
            (send msg)
            (recv (enc Nb Kab))
            (send (enc (hash Nb) Kab))
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
            ; (uniq-orig Kab) 
            (fresh-gen Kab)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Nb text) (Kab skey))
        (trace
            (recv (enc Kab a (ltk b s)))
            (send (enc Nb Kab))
            (recv (enc (hash Nb) Kab))
        )
        (constraint
            (uniq-orig Nb) (fresh-gen Nb)
            (non-orig (ltk b s))
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

(defskeleton attack
    (vars (a b s name) (Na Nb1 Nb2 text) (Kab skey) 
          (msg mesg) 
          (init_strand role_init) 
          (server_strand role_server) 
          (resp1_strand resp2_strand role_resp))

    (defstrand init 5 (a a) (b b) (s s) (Kab Kab) (Na Na) (Nb1 Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Na Na))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab) (Nb1 Nb))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab) (Nb2 Nb))

    (deftrace attack_run
        ;; session 1: legitimate run, establishes Kab
        (send-from init_strand   (cat a b Na))
        (recv-by   server_strand (cat a b Na))
        (send-from server_strand (enc Na b Kab (enc Kab a (ltk b s)) (ltk a s)))
        (recv-by   init_strand   (enc Na b Kab msg (ltk a s)))
        (send-from init_strand   msg)                       
        (recv-by   resp1_strand  (enc Kab a (ltk b s)))     
        (send-from resp1_strand  (enc Nb1 Kab))             
        (recv-by   init_strand   (enc Nb1 Kab))             
        (send-from init_strand   (enc (hash Nb1) Kab))      
        (recv-by   resp1_strand  (enc (hash Nb1) Kab))      



        ;; session 2: attack — attacker replays {Kab,A}Kbs to resp2
        ;; NOTE: attacker knows Kab (compromised), so can answer resp2's challenge
        (recv-by   resp2_strand  (enc Kab a (ltk b s)))
        (send-from resp2_strand  (enc Nb2 Kab))
        (recv-by   resp2_strand  (enc (hash Nb2) Kab))
    )
)

(defaltinstance honest_run_bounds 
    (Timeslot 10)
    (mesg 26)
    (Key 7) (name 4) (Ciphertext 6) (text 2) (tuple 6) (Hashed 1)
    (skey 7) (Attacker 1)
    (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 3) (tuple-length 5)
    (init 1) (server 1) (resp 1)
    (have-ltks)
)

(defaltinstance attack_bounds 
    (Timeslot 13)
    (mesg 37)
    (Key 7) (name 4) (Ciphertext 9) (text 4) (tuple 10) (Hashed 3)
    (skey 7) (Attacker 1)
    (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 5)
    (init 1) (server 1) (resp 2)
    (have-ltks)
)