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

;; this constraint is for generating an honest run
(defskeleton two_nonce
    (vars (a b name) (n1 n2 text) (init role_init) (resp role_resp))

    (defstrand init 3 (a a) (b b) (n1 n1))
    (defstrand resp 3 (a a) (b b) (n2 n2))

    (not-eq n1 n2)
    (non-orig (privk a) (privk b))
    (uniq-orig n1 n2)

    ;; (deftrace honest_run
    ;;   (send-from init (enc n1 (pubk b)))
    ;;   (recv-by resp (enc n1 (pubk b)))

    ;;   (send-from resp (enc n1 n2 (pubk a)))
    ;;   (recv-by init (enc n1 n2 (pubk a)))

    ;;   (send-from init (enc n2 (pubk b)))
    ;;   (recv-by resp (enc n2 (pubk b)))
    ;; )

    (deftrace attack_run
      (send-from init (enc n1 (pubk b)))
      (recv-by resp (enc n1 (pubk b)))

      (send-from resp (enc n1 n2 (pubk Attacker)))
      (recv-by init (enc n1 n2 (pubk a)))

      (send-from init (enc n2 (pubk b)))
      (recv-by resp (enc n2 (pubk b)))
    )
)
