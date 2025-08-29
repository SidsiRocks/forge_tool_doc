#lang forge/domains/crypto
(defprotocol two_nonce basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 (pubk b)))
     (recv (enc n1 n2 (pubk a)))
     (send (enc n2 (pubk b)))
     )
    )
  (defrole resp
    (vars (a b name) (n1 n2 text))
    (trace
     (recv (enc n1 (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (recv (enc n2 (pubk b)))
     )
    )
  )
(defskeleton two_nonce
  (vars (a b name) (n1 n2 text) (A role_init) (B role_resp))
  (deftrace two_nonce_trace
    (send-from A (enc n1 (pubk b)))
    (recv-by B (enc n1 (pubk b)))
    (send-from B (enc n1 n2 (pubk Attacker)))
    (recv-by B (enc n2 (pubk b)))
    (recv-by A (enc n1 n2 (pubk a)))
    (send-from A (enc n2 (pubk b)))
      ;; (send-from A (enc n1 (pubk b)))
      ;; (recv-by B (enc n1 (pubk b)))
      ;; (send-from B (enc n1 n2 (pubk a)))
      ;; (recv-by A (enc n1 n2 (pubk a)))
      ;; (send-from A (enc n2 (pubk b)))
      ;; (recv-by B (enc n2 (pubk b)))
    )
  (not-eq n1 n2)
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2)
)
