#lang forge/domains/crypto
(defprotocol addit_enc basic
    (defrole B
        (vars (a b name) (n1 n2 text))
        (trace
            (recv (cat a (enc n1 (pubk b))))
            (send (cat b (enc n2 (pubk a))))
        )
    )
  (defrole A
        (vars (a b name) (n1 n2 text))
        (trace
            (send (cat a (enc n1 (pubk b))))
            (recv (cat b (enc n2 (pubk a))))
        )
    )
)
