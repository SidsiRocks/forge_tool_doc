#lang forge/domains/crypto
;; How did this work outside of the directory\n
;; is forge implementation in PATH have to see\n
(defprotocol two_nonce basic
    (defrole resp 
        (vars (a b name) (n1 n2 text))
        (trace
            (recv (enc n1 (pubk b)))
            (send (enc n1 n2 (pubk a)))
            (recv (enc n2 (pubk b)))
        )
    )
  (defrole init
        (vars (a b name) (n1 n2 text))
        (trace
            (send (enc n1 (pubk b)))
            (recv (enc n1 n2 (pubk a)))
            (send (enc n2 (pubk b)))
        )    
    )
)
