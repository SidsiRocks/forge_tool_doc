#lang forge/domains/crypto

(defprotocol needham_schroeder_toy_prot basic 
    (defrole init 
        (vars (a b name) (n1 text))
        (trace 
            (send (cat (pubk a) (enc n1 (pubk b))))
            (recv (enc n1 (pubk a)))
        )
        (constraint 
            (non-orig (privk a))
            (uniq-orig n1)
            (fresh-gen n1)
            (not-eq a b)
        )
    )

    (defrole resp 
        (vars (a b name) (n1 text))
        (trace 
            (recv (cat (pubk a) (enc n1 (pubk b))))
            (send (enc n1 (pubk a)))
        )
        (constraint
            (non-orig (privk b))
            (not-eq a b)
        )
    )
)

(defskeleton needham_schroeder_toy_prot 
    (vars (a b name) (n1 text))
    (defstrand init 2 (a a) (b b) (n1 n1))
    ; (defstrand resp 2 (a a) (b b) (n1 n1))
)

(defaltinstance alt_single_session
  (Timeslot 4)
  (mesg 33)
  (Key 6) (name 3) (Ciphertext 10) (text 6) (tuple 8) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2) (tuple-length 2)
  (init 1) (resp 1)
)

(defaltinstance alt_double_session
  (Timeslot 8)
  (mesg 49)
  (Key 6) (name 3) (Ciphertext 15) (text 10) (tuple 15) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2) (tuple-length 2)
  (init 2) (resp 2)
)