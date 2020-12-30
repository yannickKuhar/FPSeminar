#lang racket

; da ne izgubimo funkcij `numerator` in `denominator` zaradi "naših" makrojev 
(require (rename-in racket (numerator qnumerator)(denominator qdenominator)))

#|
(provide false true zz qq .. empty s
         if-then-else
         is-zz? is-qq? is-bool? is-seq? is-proper-seq? is-empty? is-set?
         add mul leq? rounding =? right left ~ all? any?
         vars valof fun proc closure call
         gt? inv numerator denominator filtering folding mapping
         fri)
|#

; Data structure definitions.
(struct true () #:transparent)
(struct false () #:transparent)
(struct empty () #:transparent)
(struct zz (n) #:transparent)
(struct qq (e1 e2) #:transparent)
(struct .. (e1 e2) #:transparent)
(struct s (es) #:transparent)
(struct if-then-else (condition e1 e2) #:transparent)
(struct add (e1 e2) #:transparent)

; Type checking functions.
(define (is-zz? e1)
  (if (zz? e1)
      (true)
      (false)))

(define (is-qq? e1)
  (if (qq? e1)
      (true)
      (false)))

(define (is-bool? e)
  (if (or (true? e) (false? e))
      (true)
      (false)))

(define (is-seq? e)
  (if (..? e)
      (true)
      (false)))

(define (is-proper-seq? e)
  (if (..? e)
      (if (..? (..-e2 e))
          (is-proper-seq? (..-e2 e))
          (if (empty? (..-e2 e))
              (true)
              (false)))
      (false)))

(define (is-empty? e)
  (if (empty? e)
      (true)
      (false)))

(define (is-set? e)
  (if (set? e)
      (true)
      (false)))

; Operation logic functions.
(define (gcd a b)
  (if (= b 0)
      a
      (gcd b (remainder a b))))

(define (shorten a b)
  (let ([g (gcd a b)])
    (if (not (= g 1))  
      (shorten (/ a g) (/ b g))
      (cons a b))))

(define (join z1 z2)
  (if (not (..? z1))
      (.. z1 z2)
      (.. (..-e1 z1) (join (..-e2 z1) z2))))

(define (add_logic e1 e2)
  (let ([a (fr e1)]
        [b (fr e2)])
    (cond [(and (zz? a)(zz? b)) (zz (+ (zz-n a) (zz-n b)))]
          [(and (false? a) (false? b)) (false)]
          [(and (true? a) (false? b)) (true)]
          [(and (false? a) (true? b)) (true)]
          [(and (true? a) (true? b)) (true)]
          [(and (qq? a) (qq? b)) (letrec ([imen (* (qq-e2 a) (qq-e2 b))]
                                          [stev (+ (* (qq-e1 a) (qq-e2 b)) (* (qq-e1 b) (qq-e2 a)))]
                                          [sht (shorten stev imen)]) (qq (car sht) (cdr sht)))]
          [(and (qq? a) (zz? b)) (letrec ([imen (qq-e2 a)]
                                          [stev (+ (qq-e1 a) (* (qq-e2 a) (zz-n b)))]
                                          [sht (shorten stev imen)]) (qq (car sht) (cdr sht)))]
          [(and (zz? a) (qq? b)) (letrec ([imen (qq-e2 b)]
                                          [stev (+ (qq-e1 b) (* (qq-e2 b) (zz-n a)))]
                                          [sht (shorten stev imen)]) (qq (car sht) (cdr sht)))]
          [(and (..? a) (..? b)) (join a b)]
          [(and (s? a) (s? b)) (s (set-union (s-es a) (s-es b)))]
          [#t (error "add operation not supported")])))

; Main interpreter function.

(define (fr e)
  (cond [(true? e) e]
        [(false? e) e]
        [(zz? e) e]
        [(qq? e) e]
        [(empty? e) e]
        [(..? e) (.. (fr (..-e1 e)) (fr (..-e2 e)))]
        [(s? e) e]
        [(if-then-else? e) (let ([cnd (fr (if-then-else-condition e))])
                           (cond [(true? cnd) (fr (if-then-else-e1 e))]
                                 [(false? cnd) (fr (if-then-else-e2 e))]
                                 [#t (error "if-then-else condition invalid")]))]
        [(add? e) (add_logic (add-e1 e) (add-e2 e))]
        [#t (error "expression not supported by FR")]))