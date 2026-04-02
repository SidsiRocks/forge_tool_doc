#lang forge/domains/crypto

(defprotocol kao_chow_v3 basic
    (defrole init
        (vars (a b s name) (Kab Kt skey) (Na Nb text) (msg1 mesg))
        (trace
            (send (cat a b Na))
            (recv (cat (enc a b Na Kab Kt (ltk a s)) (enc Na Kab Kt) Nb msg1))
            (send (cat (enc Nb Kab Kt) msg1))
        )
        (constraint
            (non-orig (ltk a s))
            (uniq-orig Na) (fresh-gen Na)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kab Kt skey) (Na text))
        (trace 
            (recv (cat a b Na))
            (send (cat (enc a b Na Kab Kt (ltk a s)) (enc a b Na Kab Kt (ltk b s))))
        )
        (constraint
            (non-orig (ltk a s) (ltk b s))
            (uniq-orig Kab Kt) (fresh-gen Kab Kt)
            (not-eq Kab Kt)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Kab Kt skey) (Na Nb Ta text) (msg2 mesg))
        (trace
            (recv (cat msg2 (enc a b Na Kab Kt (ltk b s))))
            (send (cat msg2 (enc Na Kab Kt) Nb (enc a b Ta Kab (ltk b s))))
            (recv (cat (enc Nb Kab Kt) (enc a b Ta Kab (ltk b s))))
        )
        (constraint
            (non-orig (ltk b s))
            (uniq-orig Nb Ta) (fresh-gen Nb Ta)
            (not-eq Nb Ta)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton kao_chow_v3
    (vars (a b s name) (Kab Kt skey) (Na Nb Ta text) (msg1 msg2 mesg) (init role_init) (server role_server) (resp role_resp))
    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (Kt Kt) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (Kt Kt) (Na Na))
    (defstrand resp 3 (a a) (b b) (s s) (Kab Kab) (Kt Kt) (Na Na) (Nb Nb) (Ta Ta))

    (deftrace honest_run
        (send-from init (cat a b Na))
        (recv-by server (cat a b Na))

        (send-from server (cat (enc a b Na Kab Kt (ltk a s)) (enc a b Na Kab Kt (ltk b s))))
        (recv-by resp (cat msg2 (enc a b Na Kab Kt (ltk b s))))

        (send-from resp (cat msg2 (enc Na Kab Kt) Nb (enc a b Ta Kab (ltk b s))))
        (recv-by init (cat (enc a b Na Kab Kt (ltk a s)) (enc Na Kab Kt) Nb msg1))

        (send-from init (cat (enc Nb Kab Kt) msg1))
        (recv-by resp (cat (enc Nb Kab Kt) (enc a b Ta Kab (ltk b s))))
    )
)

(defaltinstance honest_run_bounds
    (Timeslot 8)
    (mesg 33)
    (Key 8) (name 4) (Ciphertext 7) (text 3) (tuple 11) (Hashed 0)
    (skey 8) (akey 0) (Attacker 1)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 6)
    (init 1) (server 1) (resp 1)
    (have-ltks)
)