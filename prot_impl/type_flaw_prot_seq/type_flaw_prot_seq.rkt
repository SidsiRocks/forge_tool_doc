#lang forge/domains/crypto
(defprotocol type_flaw_prot basic
  (defrole A
    (vars (a b name) (n text))
    (trace
     (send (enc (seq (pubk a) (enc n (pubk b))) (pubk b)))
     (recv (enc n (pubk a)))
    )
  )
  (defrole B
    (vars (a b name) (n text))
    (trace
     (recv (enc (seq (pubk a) (enc n (pubk b))) (pubk b)))
     (send (enc n (pubk a)))
    )
  )
)
;; These constraints generate an honest run
(defskeleton type_flaw_prot
  (vars (a b name) (n text) (A role_A) (B role_B))
  (defstrand A 2 (a a) (b b) (n n))
  (defstrand B 2 (a a) (b b))
  (non-orig (privk a) (privk b) (privk Attacker))
  (uniq-orig n)
  ;; (deftrace honest_run
  ;;   (send-from A (enc (seq (pubk a) (enc n (pubk b))) (pubk b)))
  ;;   (recv-by B (enc (seq (pubk a) (enc n (pubk b))) (pubk b)))
  ;;   (send-from B (enc n (pubk a)))
  ;;   (recv-by A (enc n (pubk a)))
  ;; )
)

(defskeleton type_flaw_prot
  (vars (a name) (n text) (A role_A) (B1 role_B) (B2 role_B))
  (defstrand A 2 (a a) (n n))
  (uniq-orig n)
  (non-orig (privk a) (privk Attacker))
)
