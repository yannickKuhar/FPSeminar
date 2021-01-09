#lang racket

(require "02-project.rkt")

(require rackunit)
(require rackunit/text-ui)

(define all-tests
  (test-suite "all"
   (test-suite "nadzor_toka"
       (test-case "add1" (check-equal?
                       (add (zz 1) (zz 2))
                       (add (zz 1) (zz 2))))
       (test-case "add2" (check-equal?
                       (fri (add (zz 1) (zz 2)) null)
                       (zz 3)))
       (test-case "add3" (check-equal?
                       (fri (add (zz 1) (zz -5)) null)
                       (zz -4)))
       (test-case "add4" (check-equal?
                       (fri (add (zz 1) (zz -5)) null)
                       (zz -4)))
       (test-case "add5" (check-equal?
                       (fri (add (zz -3476) (zz -2543)) null)
                       (zz -6019)))
       (test-case "dis1" (check-equal?
                       (fri (add (true) (true)) null)
                       (true)))
       (test-case "dis2" (check-equal?
                       (fri (add (false) (true)) null)
                       (true)))
       (test-case "dis3" (check-equal?
                       (fri (add (true) (false)) null)
                       (true)))
       (test-case "dis4" (check-equal?
                       (fri (add (false) (false)) null)
                       (false)))
       (test-case "qq1" (check-equal?
                       (fri (add (qq (zz 1) (zz 2)) (qq (zz 3) (zz 4))) null)
                       (qq (zz 5) (zz 4))))
       (test-case "qq2" (check-equal?
                       (fri (add (qq (zz -1) (zz 2)) (qq (zz 3) (zz 4))) null)
                       (qq (zz 1) (zz 4))))
       (test-case "qq3" (check-equal?
                       (fri (add (qq (zz -1) (zz 2)) (zz 1)) null)
                       (qq (zz 1) (zz 2))))
       (test-case "qq4" (check-equal?
                       (fri (add (zz 2) (qq (zz -3) (zz 4))) null)
                       (qq (zz 5) (zz 4))))
       (test-case "qq5" (check-equal?
                       (fri (add (zz 2) (inv (zz 5))) null)
                       (qq (zz 11) (zz 5))))
       )))
               
(run-tests all-tests)