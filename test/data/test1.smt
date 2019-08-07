(set-logic ALL_SUPPORTED)

; verify the well-known tautology
; (a -> b) -> ((b -> c) -> (a -> c))

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(assert (not
  (=> (=> a b)
      (=> (=> b c)
          (=> a c)))
))

(check-sat)
