#lang forge/domains/crypto
(defprotocol type_flaw_prot basic
    (defrole A
        (vars (a b name) (n text))
        (trace
            (send (enc (pubk a) (enc n (pubk b)) (pubk b)))
            (recv (enc n (pubk a)))
        )
        (constraint
            (non-orig (privk a))
            (uniq-orig n)
        )
    )
    (defrole B
        (vars (a b name) (n text))
        (trace
            (recv (enc (pubk a) (enc n (pubk b)) (pubk b)))
            (send (enc n (pubk a)))
        )
        (constraint
          (non-orig (privk b))
        )
    )
)

(defaltinstance honest_run_bounds
  (Timeslot 4)
  (mesg 24)
  (Key 6) (name 3) (Ciphertext 6) (text 3) (tuple 6) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2)
  (A 1) (B 1)
)

(defskeleton type_flaw_prot
    (vars (a b name) (n text) (A role_A) (B role_B))
    ;; (defstrand A 2 (a a) (b b) (n n))
    ;; (defstrand B 2 (a a) (b b))
    ;; (non-orig (privk a) (privk b) (privk Attacker))
    ;; (uniq-orig n)
    ;; (deftrace honest_run
    ;;   (send-from A (enc (pubk a) (enc n (pubk b)) (pubk b)))
    ;;   (recv-by   B (enc (pubk a) (enc n (pubk b)) (pubk b)))
    ;;   (send-from B (enc n (pubk a)))
    ;;   (recv-by   A (enc n (pubk a)))
    ;; )
)
