(set-info :smt-lib-version 2.6)
(set-logic QF_FP)
(set-info :category "crafted")
(set-info :source |Alberto Griggio <griggio@fbk.eu>. These benchmarks were used for the evaluation in the following paper: L. Haller, A. Griggio, M. Brain, D. Kroening: Deciding floating-point logic with systematic abstraction. FMCAD 2012. Real-numbered literals have been automatically translated by MathSAT|)
(set-info :status unknown)
;; MathSAT API call trace
;; generated on 05/20/15 17:24:51
(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun c () (_ FloatingPoint 11 53))
(define-fun rm () RoundingMode RNE)

(assert (fp.eq c (fp.add rm a (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))))

(assert (or
  (fp.eq c (fp #b0 #b10000000000 #b1111000000000000000000000000000000000000000000000000))
  (fp.eq c (fp #b0 #b10000000001 #b0001100000000000000000000000000000000000000000000000))))

(check-sat)
(exit)