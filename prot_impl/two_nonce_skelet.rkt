(defskeleton two_nonce
    (vars (a b name) (n1 n2 text))
    (defstrand init 3 (a a) (b b) (n1 n1) (n2 n2))
    (non-orig (privk a) (privk b))
    (uniq-orig n1 n2)    
)