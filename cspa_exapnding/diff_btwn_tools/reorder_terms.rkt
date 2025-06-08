#lang forge/domains/crypto
(defprotocol reorder_terms basic 
    (defrole A 
        (vars (a b name) (n1 n2 text))
        (trace 
            (send (cat n1 n2))
            (recv (cat n2 n1))
        )    
    )
    (defrole B 
        (vars (n1 n2 text) (a b name))
        (trace
            (recv (cat n2 n1))
            (send (cat n2 n1))
        )
    )
)