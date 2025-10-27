#lang forge/domains/crypto
(defprotocol hash_term_test basic
  (defrole A
    (vars (n1 text))
    (trace
      (send (cat n1))
      (recv (cat (hash n1)))
    )
  )
  (defrole B
    (vars (n1 text))
    (trace
      (recv (cat n1))
      (send (cat (hash n1)))
    )
  )
)

(defskeleton hash_term_test
  (vars (n1 text) (A role_A) (B role_B))
  (defstrand A 2 (n1 n1))
  (uniq-orig n1)

  ;; (deftrace honest_run
  ;;   (send-from A (cat n1))
  ;;   (recv-by B (cat n1))
  ;;   (send-from B (cat (hash n1)))
  ;;   (recv-by A (cat (hash n1)))
  ;; )

  ;; (deftrace imposs_run
  ;;   (recv-by B (cat n1))
  ;;   (send-from A (cat n1))
  ;;   (send-from B (cat (hash n1)))
  ;;   (recv-by A (cat (hash n1)))
  ;; )

  (deftrace poss_run
    (send-from A (cat n1))
    (recv-by B (cat n1))
    (recv-by A (cat (hash n1)))
    (send-from B (cat (hash n1)))
  )
)
