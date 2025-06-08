#lang forge/domains/crypto
(defprotocol enc_term basic 
    (defrole A 
        (vars (a b name) (n1 n2 text) (n3 n4 text))
        (trace 
            (send (enc n1 n2 (pubk a)))    
            (recv (enc n3 n4 (pubk b)))
        )
    )
    (defrole B 
        (vars (a b name) (n1 n2 text) (n3 n4 text))
        (trace
            (recv (enc n1 n2 (pubk a)))
            (send (enc n3 n4 (pubk b)))
        )
    )
)

(defskeleton enc_term
    (vars (a b name) (n1 n2 n3 n4 text))
    (defstrand A 2 (a a) (b b) (n1 n1) (n2 n2) (n3 n3) (n4 n4))
    (non-orig (privk a) (privk b))
)