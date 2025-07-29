#lang forge/domains/crypto
;; TODO removed comments of the form (comment "asdasd") for now
;; may want to change to support that later
(defprotocol ns basic
    (defrole init
        (vars (a b name ) (n1 n2 text ) )
        (trace
            (send (enc n1 (pubk b ) ) )
            (recv (enc n1 n2 (pubk a ) ) )
            (send (enc n2 (pubk b ) ) ) ) )
    (defrole resp
        (vars (b a name ) (n2 n1 text ) )
        (trace
            (recv (enc n1 (pubk b ) ) )
            (send (enc n1 n2 (pubk a ) ) )
            (recv (enc n2 (pubk b ) ) ) ) )
             )
(defskeleton ns
    (vars (a b name) (n1 n2 text) )
    (defstrand resp 3 (a a) (b b) (n2 n2) )
    (non-orig (privk a) (privk b) )
    (uniq-orig n2 n1)
 )
