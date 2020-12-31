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
(struct mul (e1 e2) #:transparent)
(struct leq? (e1 e2) #:transparent)
(struct rounding (e1) #:transparent)
(struct =? (e1 e2) #:transparent)
(struct left (e) #:transparent)
(struct right (e) #:transparent)
(struct ~ (e) #:transparent)
(struct all? (e) #:transparent)
(struct any? (e) #:transparent)

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

;;;;; Operation logic functions. ;;;;;

; Add logic.
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
          [(and (qq? a) (qq? b)) (letrec ([imen (* (zz-n (qq-e2 a)) (zz-n (qq-e2 b)))]
                                          [stev (+ (* (zz-n (qq-e1 a)) (zz-n (qq-e2 b))) (* (zz-n (qq-e1 b)) (zz-n (qq-e2 a))))]
                                          [sht (shorten stev imen)]) (qq (zz (car sht)) (zz (cdr sht))))]
          [(and (qq? a) (zz? b)) (letrec ([imen (zz-n (qq-e2 a))]
                                          [stev (+ (zz-n (qq-e1 a)) (* (zz-n (qq-e2 a)) (zz-n b)))]
                                          [sht (shorten stev imen)]) (qq (zz (car sht)) (zz (cdr sht))))]
          [(and (zz? a) (qq? b)) (letrec ([imen (zz-n (qq-e2 b))]
                                          [stev (+ (zz-n (qq-e1 b)) (* (zz-n (qq-e2 b)) (zz-n a)))]
                                          [sht (shorten stev imen)]) (qq (zz (car sht)) (zz (cdr sht))))]
          [(and (..? a) (..? b)) (join a b)]
          [(and (s? a) (s? b)) (s (set-union (s-es a) (s-es b)))]
          [#t (error "add operation not supported")])))

; Mul logic.
(define (cartps s1 s2)
  (letrec ([l1 (set->list s1)]
           [l2 (set->list s2)])
    (list->set (cartp l1 l2))))

(define (cartp l1 l2)
  (if (null? l1)
      null
      (append (make_pairs (car l1) l2) (cartp (cdr l1) l2))))
  
(define (make_pairs e l)
  (if (null? l)
      null
      (cons (cons e (car l)) (make_pairs e (cdr l)))))

(define (mul_logic e1 e2)
  (let ([a (fr e1)]
        [b (fr e2)])
    (cond [(and (zz? a)(zz? b)) (zz (* (zz-n a) (zz-n b)))]
          [(and (false? a) (false? b)) (false)]
          [(and (true? a) (false? b)) (false)]
          [(and (false? a) (true? b)) (false)]
          [(and (true? a) (true? b)) (true)]
          [(and (qq? a) (qq? b)) (letrec ([imen (* (zz-n (qq-e2 a)) (zz-n (qq-e2 b)))]
                                          [stev (* (zz-n (qq-e1 a)) (zz-n (qq-e1 b)))]
                                          [sht (shorten stev imen)]) (qq (car sht) (cdr sht)))]
          [(and (qq? a) (zz? b)) (letrec ([imen (* (zz-n (qq-e2 a)) (zz-n b))]
                                          [stev (* (zz-n (qq-e1 a)) (zz-n b))]
                                          [sht (shorten stev imen)]) (qq (car sht) (cdr sht)))]
          [(and (zz? a) (qq? b)) (letrec ([imen (* (zz-n (qq-e2 b)) (zz-n a))]
                                          [stev (* (zz-n (qq-e1 b)) (zz-n a))]
                                          [sht (shorten stev imen)]) (qq (zz (car sht)) (zz (cdr sht))))]
          [(and (s? a) (s? b)) (s (cartps (s-es a) (s-es b)))]
          [#t (error "mul operation not supported")])))

; Leq logic.
(define (zap_len zap)
  (if (or (empty? zap) (not (..? zap)))
      1
      (+ 1 (zap_len (..-e2 zap)))))

(define (leq_logic e1 e2)
  (let ([a (fr e1)]
        [b (fr e2)])
    (cond [(and (false? a) (false? b)) (true)]
          [(and (true? a) (false? b)) (false)]
          [(and (false? a) (true? b)) (true)]
          [(and (true? a) (true? b)) (true)]
          [(and (zz? a)(zz? b)) (if (<= (zz-n a) (zz-n b))
                                    (true)
                                    (false))]
          [(and (qq? a) (qq? b)) (if (<= (/ (zz-n (qq-e1 a)) (zz-n (qq-e2 a))) (/ (zz-n (qq-e1 b)) (zz-n (qq-e2 b))))
                                     (true)
                                     (false))]
          [(and (qq? a) (zz? b)) (if (<= (/ (zz-n (qq-e1 a)) (zz-n (qq-e2 a))) (zz-n b))
                                     (true)
                                     (false))]
          [(and (zz? a) (qq? b)) (if (<= (zz-n a) (/ (zz-n (qq-e1 b)) (zz-n (qq-e2 b))))
                                     (true)
                                     (false))]
          [(and (..? a) (..? b)) (if (<= (zap_len a) (zap_len b))
                                     (true)
                                     (false))]
          [(and (s? a) (s? b)) (if (subset? (s-es a) (s-es b))
                                   (true)
                                   (false))]
          [#t (error "leq? operation not supported")])))

; Rounding logic.
(define (rounding_logic e1)
  (let ([a (fr e1)])
    (cond [(zz? a) a]
          [(qq? a) (zz (exact-round (/ (zz-n (qq-e1 a)) (zz-n (qq-e2 a)))))]
          [#t (error "rounding not supported")])))

; =? logic.
(define (zap_eq z1 z2)
  (if (not (= (zap_len z1) (zap_len z2)))
      #f
      (if (and (..? z1) (..? z2))
          (and (zap_eq (..-e1 z1) (..-e1 z2)) (zap_eq (..-e2 z1) (..-e2 z2)))
          (cond [(and (true? z1) (true? z2)) #t]
                [(and (empty? z1) (empty? z2)) #t]
                [(and (false? z1) (false? z2)) #t]
                [(and (zz? z1) (zz? z2)) (= (zz-n z1) (zz-n z2))]
                [(and (qq? z1) (qq? z2)) (= (/ (zz-n (qq-e1 z1)) (zz-n (qq-e2 z1))) (/ (zz-n (qq-e1 z2)) (zz-n (qq-e2 z2))))]
                [(and (qq? z1) (zz? z2)) (= (/ (zz-n (qq-e1 z1)) (zz-n (qq-e2 z1))) (zz-n z2))]
                [(and (zz? z1) (qq? z2)) (= (/ (zz-n z1) (/ (zz-n (qq-e1 z2)) (zz-n (qq-e2 z2)))))]
                [#t #f]))))
          
(define (eq_logic e1 e2)
  (let ([a (fr e1)]
        [b (fr e2)])
    (cond [(and (false? a) (false? b)) (true)]
          [(and (true? a) (false? b)) (false)]
          [(and (false? a) (true? b)) (false)]
          [(and (true? a) (true? b)) (true)]
          [(and (zz? a)(zz? b)) (if (= (zz-n a) (zz-n b))
                                    (true)
                                    (false))]
          [(and (qq? a) (qq? b)) (if (= (/ (zz-n (qq-e1 a)) (zz-n (qq-e2 a))) (/ (zz-n (qq-e1 b)) (zz-n (qq-e2 b))))
                                     (true)
                                     (false))]
          [(and (qq? a) (zz? b)) (if (= (/ (zz-n (qq-e1 a)) (zz-n (qq-e2 a))) (zz-n b))
                                     (true)
                                     (false))]
          [(and (zz? a) (qq? b)) (if (= (zz-n a) (/ (zz-n (qq-e1 b)) (zz-n (qq-e2 b))))
                                     (true)
                                     (false))]
          [(and (..? a) (..? b)) (if (zap_eq a b)
                                     (true)
                                     (false))]
          [(and (s? a) (s? b)) (if (equal? (s-es a) (s-es b))
                                   (true)
                                   (false))])))
          
; (.. (zz 1) (.. (zz 2) (.. (zz 3) (zz 4))))

; Ecstraction loic.
(define (left_logic e1)
  (let ([a (fr e1)])
    (cond [(qq? a) (qq-e1 a)]
          [(..? a) (..-e1 a)]
          [(s? a) (set-first (s-es a))]
          [#t (error "left not supported")])))

(define (right_logic e1)
  (let ([a (fr e1)])
    (cond [(qq? a) (qq-e2 a)]
          [(..? a) (..-e2 a)]
          [(s? a) (set-rest (s-es a))]
          [#t (error "right not supported")])))

; Neg logic.
(define (neg_logic e1)
  (let ([a (fr e1)])
    (cond [(zz? a) (zz (- 0 (zz-n a)))]
          [(true? a) (false)]
          [(false? a) (true)]
          [(qq? a) (qq (qq-e2 a) (qq-e1 a))]
          [#t (error "negation not supported")])))

; All? and any? logic.
(define (all_zap zap)
  (if (..? zap)
      (and (not (equal? (..-e1 zap) (false))) (all_zap (..-e2 zap)))
      (not (equal? zap (false)))))

(define (any_zap zap)
  (if (..? zap)
      (or (not (equal? (..-e1 zap) (false))) (any_zap (..-e2 zap)))
      (not (equal? zap (false)))))

(define (any_l l)
  (if (null? l)
      #f
      (or (not (equal? (car l) (false))) (any_l (cdr l)))))
      
(define (all_logic e1)
  (let ([a (fr e1)])
    (cond [(s? a) (if (set-member? (s-es a) (false))
                      (false)
                      (true))]
          [(..? a) (if (all_zap a)
                       (true)
                       (false))]
          [#t (error "all not supported")])))

(define (any_logic e1)
  (let ([a (fr e1)])
    (cond [(s? a) (if (any_l (set->list (s-es a)))
                      (true)
                      (false))]
          [(..? a) (if (any_zap a)
                       (true)
                       (false))]
          [#t (error "any not supported")])))

; Main interpreter function.
(define (fr e)
  (letrec ([fr2 (lambda (e env)
                (cond [(true? e) e]
                      [(false? e) e]
                      [(zz? e) e]
                      [(qq? e) (if (or (= (zz-n (qq-e2 e)) 0) (= (zz-n (qq-e1 e)) (zz-n (qq-e2 e))))
                                   (error "invalid qq: denominator is 0 or numbers are not different")
                                   e)]
                      [(empty? e) e]
                      [(..? e) (.. (fr (..-e1 e)) (fr (..-e2 e)))]
                      [(s? e) e]
                      [(if-then-else? e) (let ([cnd (fr (if-then-else-condition e))])
                                           (cond [(true? cnd) (fr (if-then-else-e1 e))]
                                                 [(false? cnd) (fr (if-then-else-e2 e))]
                                                 [#t (error "if-then-else condition invalid")]))]
                      [(add? e) (add_logic (add-e1 e) (add-e2 e))]
                      [(mul? e) (mul_logic (mul-e1 e) (mul-e2 e))]
                      [(leq?? e) (leq_logic (leq?-e1 e) (leq?-e2 e))]
                      [(rounding? e) (rounding_logic (rounding-e1 e))]
                      [(=?? e) (eq_logic (=?-e1 e) (=?-e2 e))]
                      [(left? e) (left_logic (left-e e))]
                      [(right? e) (right_logic (right-e e))]
                      [(~? e) (neg_logic (~-e e))]
                      [(all?? e) (all_logic (all?-e e))]
                      [(any?? e) (any_logic (any?-e e))]
                      [#t (error "expression not supported by FR")]))])
    (fr2 e null)))
