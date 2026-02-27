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

(defaltinstance alt_tmn_small
  (Timeslot 8)
  (mesg 33)
  (Key 11) (name 4) (Ciphertext 8) (text 4) (tuple 6) (Hashed 0)
  (akey 8) (skey 3) (Attacker 1)
  (PublicKey 4) (PrivateKey 4)
  (enc-depth 2) (tuple-length 2)
  (init 1) (resp 1) (server 1)
)

(defaltinstance alt_tmn_attack  
  (Timeslot 8)
  (mesg 33)
  (Key 11) (name 4) (Ciphertext 8) (text 4) (tuple 6) (Hashed 0)
  (akey 8) (skey 3) (Attacker 1)
  (PublicKey 4) (PrivateKey 4)
  (enc-depth 2) (tuple-length 2)
  (init 1) (resp 1) (server 1)
)