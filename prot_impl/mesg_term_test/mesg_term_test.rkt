#lang forge/domains/crypto
;; TODO ask what this basic is about
(defprotocol mesg_term_test basic
  (defrole A
    (vars (a b name) (n1 text))
    (trace
     (send (enc n1 (pubk a)))
     (recv (enc n1 (pubk a)))
    )
  )
  ;; this m will work but it cannot correspond to multiple terms like
  ;; if it was (cat (enc n1 (pubk a)) (enc n2 (pubk a))) this wouldn't work
  (defrole B
    (vars (a b name) (m mesg))
    (trace
     (recv m)
     (send m)
    )
  )
)
