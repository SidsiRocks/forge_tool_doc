#lang forge/domains/crypto

(defprotocol simple_enc basic
    (defrole init 
        (vars (a b name))
        (trace 
            (send (enc a (pubk b)))
            (recv (enc b (pubk a)))
        ))
    (defrole resp 
        (vars (a b name))
        (trace
            (recv (enc a (pubk b)))
            (send (enc b (pubk a)))
        )
    )
)

(defskeleton simple_enc
  (vars (a b name))
  (defstrand init 2 (a a) (b b))
  (defstrand resp 2 (a a) (b b))
)


