#lang forge/domains/crypto
(defprotocol type_flaw_prot basic
  (defrole A
    (vars (a b name) (n text))
    (trace
     (send (enc (pubk a) (enc n (pubk b)) (pubk b)))
     (recv (enc n (pubk a)))
     )
    )
  (defrole B
    (vars (a b name) (n text))
    (trace
     (recv (enc (pubk a) (enc n (pubk b)) (pubk b)))
     (send (enc n (pubk a)))
     )
    )
)

(defskeleton type_flaw_prot
  (vars (a b name) (n text) (A role_A) (B role_B))

  (defstrand A 2 (a a) (n n))

  ;; TODO check if non-orig privk Attacker is needed or not
  (non-orig (privk a) (privk b) (privk Attacker))
  (uniq-orig n)
)
