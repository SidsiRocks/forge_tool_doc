#lang forge/domains/crypto
(defprotocol nested_seq_test basic
  (defrole A
    (vars (a b name) (n0 n1 text))
    (trace
     (send (enc (seq (pubk a) (enc n0 (pubk b))) (pubk b)))
     (recv (enc (seq (pubk a) n1) (pubk a)))
     )
  )
  (defrole B
    (vars (a b name) (n0 text))
    (trace
     (recv (enc (seq (pubk a) (enc n0 (pubk b))) (pubk b)))
     (send (enc (seq (pubk a)
                     (enc (seq (pubk a) (enc n0 (pubk b))) (pubk b)))
                (pubk a)))
    )
  )
)
(defskeleton nested_seq_test
  (vars (a name) (b name) (n0 text))
  (defstrand A 2 (a a) (n0 n0))
  (defstrand B 2 (a a) (b b))
  (uniq-orig n0)
  (non-orig (privk a) (privk Attacker) (privk b))
)
