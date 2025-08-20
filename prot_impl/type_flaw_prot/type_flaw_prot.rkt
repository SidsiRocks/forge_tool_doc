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
    (vars (a b name) (n text))
    (defstrand A 2 (a a) (b b) (n n))
    (non-orig (privk a) (privk b))
    (uniq-orig n)
)