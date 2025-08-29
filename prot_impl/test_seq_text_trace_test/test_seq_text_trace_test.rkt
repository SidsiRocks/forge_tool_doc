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
(defskeleton test_seq_text
  (vars (a b name) (n1 n2 text) (A role_A) (B role_B))
  (defstrand A 2 (a a) (b b))
  ;; (deftrace honest_run
  ;;   (send-from A (enc n1 (pubk b)))
  ;;   (recv-by B (enc n1 (pubk b)))

  ;;   ;; (send-from B (cat (pubk a) (enc n1 (pubk b))))
  ;;   ;; (recv-by A (seq (pubk a) (enc n1 (pubk b))))
  ;; )
  (non-orig (pubk a) (pubk b))
  ;; (uniq-orig n1 n2)
)
