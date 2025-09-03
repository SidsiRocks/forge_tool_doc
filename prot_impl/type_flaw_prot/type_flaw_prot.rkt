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
    (defstrand A 2 (a a) (b b) (n n))
    (defstrand B 2 (a a) (b b))
    (non-orig (privk a) (privk b) (privk Attacker))
    (uniq-orig n)
    (deftrace honest_run
      (send-from A (enc (pubk a) (enc n (pubk b)) (pubk b)))
      (recv-by   B (enc (pubk a) (enc n (pubk b)) (pubk b)))
      (send-from B (enc n (pubk a)))
      (recv-by   A (enc n (pubk a)))
    )
)
