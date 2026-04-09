#lang forge/domains/crypto

(defprotocol denning_saco basic
    (defrole init
        (vars (a b s name) (Kab skey) (T text) (msg mesg))
        (trace
            (send (cat a b))
            (recv (enc b Kab T msg (ltk a s)))
            (send msg)
        )
        (constraint
            (non-orig (ltk a s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kab skey) (T text))
        (trace
            (recv (cat a b))
            (send (enc b Kab T (enc Kab a T (ltk b s)) (ltk a s)))
        )
        (constraint
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
            (recv (enc Kab a T (ltk b s)))
        )
        (constraint
            (non-orig (ltk b s))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton denning_saco
    (vars (a b s name) (Kab skey) (T text) (msg mesg) (init role_init) (server role_server) (resp role_resp))
    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand resp 1 (a a) (b b) (s s) (Kab Kab) (T T))

    (deftrace honest_run
        (send-from init (cat a b))
        (recv-by server (cat a b))

        (send-from server (enc b Kab T (enc Kab a T (ltk b s)) (ltk a s)))
        (recv-by init (enc b Kab T msg (ltk a s)))

        (send-from init msg)
        (recv-by resp (enc Kab a T (ltk b s)))
    )
)

(defskeleton attack
    (vars (a b s name) (Kab skey) (T text) (msg mesg)
          (init role_init) (server role_server)
          (resp1 resp2 role_resp))

    (defstrand init 3 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand server 2 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand resp 1 (a a) (b b) (s s) (Kab Kab) (T T))
    (defstrand resp 1 (a a) (b b) (s s) (Kab Kab) (T T))

    ; (deftrace attack_run
    ;     (send-from init (cat a b))
    ;     (recv-by server (cat a b))

    ;     (send-from server (enc b Kab T (enc Kab a T (ltk b s)) (ltk a s)))
    ;     (recv-by init (enc b Kab T msg (ltk a s)))

    ;     (send-from init msg)
    ;     (recv-by resp1 (enc Kab a T (ltk b s)))

    ;     ;; replay into a second session
    ;     (recv-by resp2 (enc Kab a T (ltk b s)))
    ; )
)

(defaltinstance honest_run_bounds
    (Timeslot 6)
    (mesg 25)
    (Key 7) (name 4) (Ciphertext 6) (text 2) (tuple 6) (Hashed 0) 
    (akey 0) (skey 7) (Attacker 1)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 5)
    (init 1) (server 1) (resp 1)
    (have-ltks)
)

(defaltinstance attack_bounds
    (Timeslot 7)
    (mesg 25)
    (Key 7) (name 4) (Ciphertext 6) (text 2) (tuple 6) (Hashed 0)
    (akey 0) (skey 7) (Attacker 1)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 2) (tuple-length 5)
    (init 1) (server 1) (resp 2)
    (have-ltks)
)