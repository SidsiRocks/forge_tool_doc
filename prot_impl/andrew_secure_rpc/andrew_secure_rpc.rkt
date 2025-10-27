#lang forge/domains/crypto
(defprotocol andrew_secure_rpc basic
  (defrole A
    (vars (a b name) (kab_ skey) (na nb nb_ text))
    (trace
     (send (cat a (enc na (ltk a b))))
     (recv (enc (hash na) nb (ltk a b)))
     (send (enc (hash nb) (ltk a b)))
     (recv (enc kab_ nb_ (ltk a b)))
    )
  )
  (defrole B
    (vars (a b name) (kab_ skey) (na nb nb_ text))
    (trace
     (recv (cat a (enc na (ltk a b))))
     (send (enc (hash na) nb (ltk a b)))
     (recv (enc (hash nb) (ltk a b)))
     (send (enc kab_ nb_ (ltk a b)))
    )
  )
)

(defskeleton andrew_secure_rpc
  (vars (a b name) (kab_ skey) (na text))

  ;; correct constraints ensures A believes it communicates with A
  ;; and B communicates with B
  ;; defstrand only works for one strand so manually
  ;; adding constraint to be uniq-orig and non-orig separetly

  ;; (deftrace honest_run
  ;;   (send-from A (cat a (enc na (ltk a b))))
  ;;   (recv-by B (cat a (enc na (ltk a b))))
  ;;   (send-from B (enc (hash na) nb (ltk a b)))
  ;;   (recv-by A (enc (hash na) nb (ltk a b)))
  ;;   (send-from A (enc (hash nb) (ltk a b)))
  ;;   (recv-by B (enc (hash nb) (ltk a b)))
  ;;   (send-from B (enc kab_ nb_ (ltk a b)))
  ;;   (recv-by A (enc kab_ nb_ (ltk a b)))
  ;; )
)
