#lang forge/domains/crypto
(defprotocol two_nonce basic
    (defrole init
        (vars (a b name) (n1 n2 text))
        (trace
            (send (enc n1 (pubk b)))
            (recv (enc n1 n2 (pubk a)))
            (send (enc n2 (pubk b)))
        )
        (constraint
           (non-orig (privk a))
           (uniq-orig n1)
           (fresh-gen n1)
           (not-eq n1 n2)
        )
    )
    (defrole resp
        (vars (a b name) (n1 n2 text))
        (trace
            (recv (enc n1 (pubk b)))
            (send (enc n1 n2 (pubk a)))
            (recv (enc n2 (pubk b)))
        )
        (constraint
             (non-orig (privk b))
             (uniq-orig n2)
             (fresh-gen n2)
        )
    )
)
(defskeleton two_nonce
    (vars (a b name) (n1 n2 text))
    (defstrand init 3 (a a) (b b) (n1 n1) (n2 n2))
    ;; (non-orig (privk a) (privk b))
    ;; (uniq-orig n1 n2)
)

(defaltinstance alt_single_session
  (Timeslot 6)
  (mesg 33)
  (Key 6) (name 3) (Ciphertext 10) (text 6) (tuple 8) (Hashed 0) ;; in tuple model Hashed has to be 0 currently as only storing hashed model
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2) (tuple-length 2)
  (init 1) (resp 1)
  )

(defaltinstance alt_double_session
  (Timeslot 12)
  (mesg 49)
  (Key 6) (name 3) (Ciphertext 15) (text 10) (tuple 15) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2) (tuple-length 2)
  (init 2) (resp 2)
)
;; (definstance single_session
;;   (Timeslot 6)
;;   (mesg 25)
;;   (Key 6) (name 3) (Ciphertext 10) (text 6) (Hashed 0)
;;   (akey 6) (skey 0) (Attacker 1)
;;   (PublicKey 3) (PrivateKey 3)
;;   (enc-depth 2)
;;   (init 1) (resp 1)
;; )

;; (definstance two_sessions
;;   (Timeslot 12)
;;   (mesg 29)
;;   (Key 6) (name 3) (Ciphertext 10) (text 10) (Hashed 0)
;;   (akey 6) (skey 0) (Attacker 1)
;;   (PublicKey 3) (PrivateKey 3)
;;   (enc-depth 2)
;;   (init 2) (resp 2)
;; )

