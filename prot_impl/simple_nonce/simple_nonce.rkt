#lang forge/domains/crypto

(defprotocol simple_nonce basic 
    (defrole init 
        (vars (a b name) (n1 text))
        (trace 
            (send (enc n1 (pubk b)))
            (recv (enc n1 (pubk a)))
        ))
    (defrole resp 
        (vars (a b name) (n1 text))
        (trace 
            (recv (enc n1 (pubk b)))
            (send (enc n1 (pubk a)))
        ))
)
(defskeleton simple_nonce
    (vars (a b name) (n1 text))
    (defstrand init 2 (a a) (b b) (n1 n1))
    (non-orig (privk a) (privk b))
    (uniq-orig n1)
)