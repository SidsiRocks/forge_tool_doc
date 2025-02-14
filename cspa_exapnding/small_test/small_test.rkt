#lang forge/domains/crypto
(defprotocol small_test basic 
    (defrole B 
        (vars (a b name) (n1 n2 text))
        (trace
            (recv (cat a n1))
            (send (cat b n2))
        )
    )
  (defrole A 
        (vars (a b name) (n1 n2 text))
        (trace
            (send (cat a n1))
            (recv (cat b n2))
        )
    )
)
