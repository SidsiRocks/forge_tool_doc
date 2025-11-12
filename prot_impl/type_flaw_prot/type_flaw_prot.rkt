#lang forge/domains/crypto
(defprotocol type_flaw_prot basic
    (defrole A
        (vars (a b name) (n text))
        (trace
            (send (enc (pubk a) (enc n (pubk b)) (pubk b)))
            (recv (enc n (pubk a)))
        )
        (constraint
            (non-orig (privk a))
            (uniq-orig n)
        )
    )
    (defrole B
        (vars (a b name) (n mesg))
        (trace
            (recv (enc (pubk a) (enc_no_tpl n (pubk b)) (pubk b)))
            (send (enc_no_tpl n (pubk a)))
        )
        (constraint
          (non-orig (privk b))
        )
    )
)

(defaltinstance honest_run_bounds
  (Timeslot 4)
  (mesg 24)
  (Key 6) (name 3) (Ciphertext 6) (text 3) (tuple 6) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2) (tuple-length 2)
  (A 1) (B 1)
)

(defaltinstance attack_run_bounds
  (Timeslot 6)
  (mesg 36)
  (Key 6) (name 3) (Ciphertext 12) (text 3) (tuple 12) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 3) (tuple-length 2)
  (A 1) (B 2)
)

(defaltinstance smaller_attack_bound
  (Timeslot 6)
  (mesg 23)
  (Key 6) (name 3) (Ciphertext 7) (text 3) (tuple 4) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 3) (tuple-length 2)
  (A 1) (B 2)
)

(defaltinstance larger_attack_bound
  (Timeslot 6)
  (mesg 34)
  (Key 6) (name 3) (Ciphertext 14) (text 3) (tuple 8) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 3) (tuple-length 2)
  (A 1) (B 2)
)

(defskeleton type_flaw_prot
    (vars (a b name) (n text) (A role_A) (B1 B2 role_B))
    ;; (defstrand A 2 (a a) (b b) (n n))
    ;; (defstrand B 2 (a a) (b b))
    ;; (non-orig (privk a) (privk b) (privk Attacker))
    ;; (uniq-orig n)
    ;; (deftrace honest_run
    ;;     (send-from A (enc (pubk a) (enc n (pubk b)) (pubk b)))
    ;;     (recv-by   B1 (enc (pubk a) (enc n (pubk b)) (pubk b)))
    ;;     (send-from B1 (enc n (pubk a)))
    ;;     (recv-by   A (enc n (pubk a)))
    ;; )

    ;; (deftrace attack_run
    ;;   (send-from A (enc (pubk a) (enc n (pubk b)) (pubk b)))

    ;;   (recv-by B1 (enc (pubk Attacker)
    ;;                    (enc (pubk a) (enc n (pubk b)) (pubk b))
    ;;                    (pubk b)))
    ;;   (send-from B1 (enc (pubk a) (enc n (pubk b)) (pubk Attacker)))

    ;;   (recv-by B2 (enc (pubk Attacker) (enc n (pubk b)) (pubk b)))
    ;;   (send-from B2 (enc n (pubk Attacker)))
    ;; )
)

;; adding comment here so can make new commit with commit message which shows that
;; can generate type flaw attack now

