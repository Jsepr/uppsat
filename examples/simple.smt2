(set-info :smt-lib-version 2.6)
(set-logic QF_FP)
(set-info :category "crafted")
(set-info :source |Alberto Griggio <griggio@fbk.eu>. These benchmarks were used for the evaluation in the following paper: L. Haller, A. Griggio, M. Brain, D. Kroening: Deciding floating-point logic with systematic abstraction. FMCAD 2012. Real-numbered literals have been automatically translated by MathSAT|)
(set-info :status unknown)
;; MathSAT API call trace
;; generated on 05/20/15 17:24:51

(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
(define-fun rm () RoundingMode RNE)

(define-fun sum () (_ FloatingPoint 11 53) (fp.add rm a b))
(define-fun c () (_ FloatingPoint 11 53) (fp #b0 #b10000001000 #b1111111000010000000000000000000000000000000000000000))

(assert (fp.gt a (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))
(assert (fp.gt b (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))
(assert (fp.gt sum c))

(check-sat)
(exit)
