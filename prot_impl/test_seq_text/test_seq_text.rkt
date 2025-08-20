#lang forge/domains/crypto
(defprotocol test_seq_text basic
    (defrole A 
        (vars (a b name) (n1 n2 text))
        (trace
            (send (enc n1 (pubk b)))
            (recv n2)
        )
    )
    (defrole B
        (vars (a b name) (n1 text))
        (trace
            (recv (enc n1 (pubk b)))
            (send (cat (pubk a) (enc n1 (pubk b))))
        )
    )
)