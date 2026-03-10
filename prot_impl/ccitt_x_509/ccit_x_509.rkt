#lang forge/domains/crypto
;; page 11 in complete SPORE repository reference
(defprotocol ccit_x_509 basic
  (defrole A
    (vars (a b name) (Ta Tb Na Nb text) (Ya Yb Xa Xb text))
    (trace
     (send (cat a (enc Ta Na b Xa (enc Ya (pubk b)) (privk a))))
     (recv (cat b (enc Tb Nb a Na Xb (enc Yb (pubk a)) (privk b))))
     (send (cat a (enc Nb (privk a))))
     )
    (constraint
     (non-orig (privk a))
     (uniq-orig Ta Na Xa Ya)
     (fresh-gen Ta Na Xa Ya)
     (not-eq Ta Na) (not-eq Ta Xa) (not-eq Ta Ya)
     (not-eq Na Xa) (not-eq Na Ya)
     (not-eq Xa Ya)
    )
  )
  (defrole B
    (vars (a b name) (Ta Tb Na Nb text) (Ya Yb Xa Xb text))
    (trace
     (recv (cat a (enc Ta Na b Xa (enc Ya (pubk b)) (privk a))))
     (send (cat b (enc Tb Nb a Na Xb (enc Yb (pubk a)) (privk b))))
     (recv (cat a (enc Nb (privk a))))
     )
    (constraint
     (non-orig (privk b))
     (uniq-orig Tb Nb Xb Yb)
     (fresh-gen Tb Nb Xb Yb)
     ;; TODO modify parsers to parse not-eq with multiple constraints
     ;; also can apply not-eq constraint without all existential quanitification
     (not-eq Tb Nb) (not-eq Tb Xb) (not-eq Tb Yb)
     (not-eq Nb Xb) (not-eq Nb Yb)
     (not-eq Xb Yb)
    )
  )
)

(defaltinstance honest_run_test
  (Timeslot 6)
  (mesg 43)
  ;; ciphertext min 5 keeping 10
  ;;text min 8 keeping 12
  ;; tuple min 8 keeping 12
  ;; hashed min 0 keeping 0
  ;; 6 + 3 + 10 + 12 + 12 = 43
  (Key 6) (name 3) (Ciphertext 10) (text 12) (tuple 12) (Hashed 0)
  (akey 6) (skey 0) (Attacker 1)
  (PublicKey 3) (PrivateKey 3)
  (enc-depth 2) (tuple-length 6)
  (A 1) (B 1)
)
