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
    (constraint
      (non-orig (ltk a b))
      (uniq-orig na)
      (fresh-gen na)
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
    (constraint
     (non-orig (ltk a b))
     (uniq-orig nb nb_ kab_)
     (fresh-gen nb nb_ kab_)
    )
  )
)

(defaltinstance honest_run_bounds
  (Timeslot 8)
  (mesg 34)
  (Key 3) (name 3) (Ciphertext 8) (text 6) (tuple 10) (Hashed 4)
  (akey 0) (skey 3) (Attacker 1)
  (PublicKey 0) (PrivateKey 0)
  (enc-depth 1) (tuple-length 2)
  (A 1) (B 1)
  (have-ltks)
)

(defaltinstance attack_run_bounds
  (Timeslot 16)
  (mesg 35)
  (Key 4) (name 3) (Ciphertext 8) (text 6) (tuple 10) (Hashed 4)
  (akey 0) (skey 4) (Attacker 1)
  (PublicKey 0) (PrivateKey 0)
  (enc-depth 1) (tuple-length 2)
  (A 2) (B 2)
  (have-ltks)
)

(defskeleton andrew_secure_rpc
  (vars (a b name) (kab_ skey) (na nb nb_ text)
        (kab_1 skey) (na1 nb1 nb_1 text)
        (A A1 role_A) (B B1 role_B))

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

  (deftrace large_honest_run
     (send-from A (cat a (enc na (ltk a b))))
     (recv-by B (cat a (enc na (ltk a b))))
     (send-from B (enc (hash na) nb (ltk a b)))
     (recv-by A (enc (hash na) nb (ltk a b)))
     (send-from A (enc (hash nb) (ltk a b)))
     (recv-by B (enc (hash nb) (ltk a b)))
     (send-from B (enc kab_ nb_ (ltk a b)))
     (recv-by A (enc kab_ nb_ (ltk a b)))

     (send-from A1 (cat a (enc na1 (ltk a b))))
     (recv-by B1 (cat a (enc na1 (ltk a b))))
     (send-from B1 (enc (hash na1) nb1 (ltk a b)))
     (recv-by A1 (enc (hash na1) nb1 (ltk a b)))
     (send-from A1 (enc (hash nb1) (ltk a b)))
     (recv-by B1 (enc (hash nb1) (ltk a b)))
     (send-from B1 (enc kab_1 nb_1 (ltk a b)))
     (recv-by A1 (enc kab_1 nb_1 (ltk a b)))
  )
)
