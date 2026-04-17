#lang forge/domains/crypto

;; TODO add constraint for name (like a) to be own name, not always needed
;; but needed here so that b is not sending their own name for example

(defprotocol tmn basic
    (defrole init
        (vars (a b s name) (Ka Kb skey))
        (trace
            (send (cat b (enc Ka (pubk s))))
            (recv (cat b (enc Kb Ka)))
        )
        (constraint
            (uniq-orig Ka)
            (fresh-gen Ka)
            (non-orig (privk a))
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
    (defrole resp
        (vars (a b s name) (Kb Ka skey))
        (trace 
            (recv a)
            (send (cat a (enc Kb (pubk s))))
        )
        (constraint
            (uniq-orig Kb)
            (fresh-gen Kb)
            (non-orig (privk b))
            (not-eq a b) (not-eq a s) (not-eq b s)
            ; (not-eq a Attacker) (not-eq b Attacker) (not-eq s Attacker)
        )
    )
    (defrole server
        (vars (a b s name) (Ka Kb skey))
        (trace
            (recv (cat b (enc Ka (pubk s))))
            (send a)
            (recv (cat a (enc Kb (pubk s))))
            (send (cat b (enc Kb Ka)))
        )
        (constraint
            (non-orig (privk s))
            (not-eq a b) (not-eq a s) (not-eq b s)
            (not-eq Ka Kb)
            ; (not-eq a Attacker) (not-eq b Attacker) (not-eq s Attacker)
        )
    )
)

(defskeleton tmn
    (vars (a b s name) (Ka Kb skey))
    (defstrand init 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand resp 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand server 4 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    ; (uniq-orig Ka)
    ; (not-eq a b)
    ; (not-eq a s)
    ; (not-eq b s)
    ; (uniq-orig Kb)
)

(defskeleton attack1 
    (vars (a b s name) (Ka Kb skey) (server_strand role_server) (resp_strand role_resp))
    ; (defstrand init 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand resp 2 (a a) (b b) (s s) (Kb Kb))
    (defstrand server 4 (a a) (b b) (s s) (Ka Ka) (Kb Kb))

    (deftrace attack_trace 
        (recv-by server_strand (cat b (enc Ka (pubk s))))
        (send-from server_strand a)
        (recv-by resp_strand a)
    )
)

(defskeleton attack2 
    (vars (a b s name) (Ka Kb skey) (server_strand role_server))
    (defstrand init 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    ; (defstrand resp 2 (a a) (b b) (s s) (Kb Kb))
    (defstrand server 4 (a a) (b b) (s s) (Ka Ka) (Kb Kb))

    ; (deftrace attack_trace 
    ;     (recv-by server_strand (cat b (enc Ka (pubk s))))
    ;     (send-from server_strand a)
    ; )
)

(defskeleton attack3 
    (vars (a b s name) (Ka Kb skey))
    (defstrand server 4 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand resp 2 (a a) (b b) (s s) (Kb Kb))
    (defstrand server 4 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand init 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
)

(defaltinstance alt_tmn_small
  (Timeslot 8)
  (mesg 33)
  (Key 11) (name 4) (Ciphertext 8) (text 4) (tuple 6) (Hashed 0)
  (akey 8) (skey 3) (Attacker 1)
  (PublicKey 4) (PrivateKey 4)
  (enc-depth 2) (tuple-length 2)
  (init 1) (resp 1) (server 1)
)

(defaltinstance alt_tmn_attack1
  (Timeslot 6)
  (mesg 24)
  (Key 10) (name 4) (Ciphertext 3) (text 0) (tuple 7) (Hashed 0)
  (akey 8) (skey 2)
  (PublicKey 4) (PrivateKey 4)
  (enc-depth 2) (tuple-length 2)
  (init 1) (resp 1) (server 1) (Attacker 1)
)

(defaltinstance alt_tmn_attack2 
    (Timeslot 12)
    (mesg 35)
    (Key 11) (name 4) (Ciphertext 6) (text 0) (tuple 14) (Hashed 0)
    (akey 8) (skey 3)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 2)
    (init 1) (resp 1) (server 2) (Attacker 1)
)