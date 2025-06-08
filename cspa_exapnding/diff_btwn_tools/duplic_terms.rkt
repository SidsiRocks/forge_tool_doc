#lang forge/domains/crypto
(defprotocol duplic_terms basic
    (defrole A
        (vars (n1 n2 text))
        (trace
            (send (cat n1))
            (recv (cat n1 n2))
        )
    )
    (defrole B
        (vars (n1 n2 text))
        (trace
            (recv (cat n1 n2))
            (send (cat n2))
        )
    )
)