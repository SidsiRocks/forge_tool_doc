#lang forge/domains/crypto
(defprotocol new_reorder_terms basic 
    (defrole A 
        (vars (a b name) (n1 n2 text))
        (trace
            (send (enc n1 n2 (ltk a b)))
            (recv (enc n1 (ltk a b)))
        )
    )
    (defrole B 
        (vars (a b name) (n1 n2 text))
        (trace
            (recv (enc n1 n2 (ltk a b)))
            (send (enc n1 (ltk a b)))
        )
    )
)

(defskeleton new_reorder_terms
    (vars (a b name) (n1 n2 text))
    (defstrand A 2 (a a) (b b) (n1 n1) (n2 n2))
    (non-orig (ltk a b))
    (uniq-orig n1 n2)
)

(defskeleton new_reorder_terms
    (vars (a b name) (n1 n2 text))
    (defstrand B 2 (a a) (b b) (n1 n1) (n2 n2))
    (non-orig (ltk a b))
    (uniq-orig n1 n2)
)