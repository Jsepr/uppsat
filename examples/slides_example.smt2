(set-info :smt-lib-version 2.6)
(set-logic QF_FP)
(set-info :category "crafted")
(set-info :source |Alberto Griggio <griggio@fbk.eu>. These benchmarks were used for the evaluation in the following paper: L. Haller, A. Griggio, M. Brain, D. Kroening: Deciding floating-point logic with systematic abstraction. FMCAD 2012. Real-numbered literals have been automatically translated by MathSAT|)
(set-info :status unknown)
;; MathSAT API call trace
;; generated on 05/20/15 17:24:51
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(define-fun rm () RoundingMode RNE)

(assert (fp.eq y (fp.add rm x (fp #b0 #b01111111111 #b1100000000000000000000000000000000000000000000000000))))
(assert (fp.gt y (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))
(assert (or
  (fp.eq x (fp #b0 #b10000000000 #b0000000000000000000000000000000000000000000000000000))
  (fp.eq x (fp #b1 #b10000000001 #b0000000000000000000000000000000000000000000000000000))))

(check-sat)
(exit)