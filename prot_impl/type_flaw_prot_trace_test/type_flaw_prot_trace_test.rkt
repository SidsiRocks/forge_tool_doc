#lang forge/domains/crypto
(defprotocol type_flaw_prot basic
  (defrole A
    (vars (a b name) (n text))
    (trace
     (send (enc (pubk a) (enc n (pubk b)) (pubk b)))
     (recv (enc n (pubk a)))
     )
    )
  (defrole B
    (vars (a b name) (n text))
    (trace
     (recv (enc (pubk a) (enc n (pubk b)) (pubk b)))
     (send (enc n (pubk a)))
     )
    )
)

(defskeleton type_flaw_prot
  (vars (a b name) (n text) (A role_A) (B1 role_B) (B2 role_B))
  ;; TODO can write not-eq for these yet might not be necessary will
  ;; change parser and transcribe to fix this
  ;; (not-eq B1 B2)

  (defstrand A 2 (a a) (n n))
  (defstrand B 2 (b b))
  ;; TODO check if non-orig privk Attacker is needed or not
  (non-orig (privk a) (privk b) (privk Attacker))
  (uniq-orig n)

   (deftrace type_flaw_attack
     (send-from A (enc (pubk a) (enc n (pubk b)) (pubk b)))
     ;; (recv-by B1 (enc (pubk Attacker)
     ;;   (enc (seq (pubk a) (enc n (pubk b))) (pubk b))
     ;;   (pubk b)
     ;;  )
     ;; )
     ;; (send-from B1 (enc (seq (pubk a) (enc n (pubk b))) (pubk b)))
     ;; (recv-by B2 (enc (pubk Attacker) (enc n (pubk b))) (pubk b))
     ;; (send-by B2 (enc n (pubk Attacker)))
     ;; (recv-by A (enc n (pubk a)))
   )
)
