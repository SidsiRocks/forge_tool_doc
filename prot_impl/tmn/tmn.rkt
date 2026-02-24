#lang forge/domains/crypto
(defprotocol tmn basic
    (defrole init
        (vars (a b s name) (Ka Kb skey))
        (trace
            (send (cat b (enc Ka (pubk s))))
            (recv (cat b (enc Kb Ka)))
        )
        (constraint
            (uniq-orig Ka)
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
        )
    )
)

(defskeleton tmn
    (vars (a b s name) (Ka Kb skey))
    (defstrand init 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand resp 2 (a a) (b b) (s s) (Ka Ka) (Kb Kb))
    (defstrand server 4 (a a) (b b) (s s) (Ka Ka) (Kb Kb))

    (not-eq a b)
    (not-eq a s)
    (not-eq b s)
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