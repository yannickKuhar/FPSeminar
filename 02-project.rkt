#lang racket

; da ne izgubimo funkcij `numerator` in `denominator` zaradi "naših" makrojev 
(require (rename-in racket (numerator qnumerator)(denominator qdenominator)))
(require racket/trace)

(provide false true zz qq .. empty s
         if-then-else
         is-zz? is-qq? is-bool? is-seq? is-proper-seq? is-empty? is-set?
         add mul leq? rounding =? right left ~ all? any?
         vars valof fun proc closure call
         gt? inv numerator denominator filtering folding mapping
         fri)

; Data structure definitions.
(struct true () #:transparent)
(struct false () #:transparent)
(struct empty () #:transparent)
(struct zz (n) #:transparent)
(struct qq (e1 e2) #:transparent)
(struct .. (e1 e2) #:transparent)
(struct s (es) #:transparent)
(struct if-then-else (condition e1 e2) #:transparent)
(struct is-zz? (e1) #:transparent)
(struct is-qq? (e1) #:transparent)
(struct is-bool? (e1) #:transparent)
(struct is-seq? (e1) #:transparent)
(struct is-proper-seq? (e1) #:transparent)
(struct is-empty? (e1) #:transparent)
(struct is-set? (e1) #:transparent)
(struct add (e1 e2) #:transparent)
(struct mul (e1 e2) #:transparent)
(struct leq? (e1 e2) #:transparent)
(struct rounding (e1) #:transparent)
(struct =? (e1 e2) #:transparent)
(struct left (e1) #:transparent) 
(struct right (e1) #:transparent)
(struct ~ (e1) #:transparent)
(struct all? (e1) #:transparent)
(struct any? (e1) #:transparent)
(struct vars (s e1 e2) #:transparent)
(struct valof (s) #:transparent)

(struct closure (env f) #:transparent) ; TODO: Remove transparent
(struct fun (name farg body) #:transparent)
(struct proc (name body) #:transparent)
(struct call (e args) #:transparent)

; General helpers.
(define (qq_format e)
  (cond [(qq? e) (if (or (= (zz-n (qq-e2 e)) 0))
                     (error "invalid qq: denominator is 0")
                      (cond [(or (and (> (zz-n (qq-e1 e)) 0) (< (zz-n (qq-e2 e)) 0))
                                 (and (< (zz-n (qq-e1 e)) 0) (< (zz-n (qq-e2 e)) 0)))
                             (qq (zz (- 0 (zz-n (qq-e1 e)))) (zz (- 0 (zz-n (qq-e2 e)))))]
                            [#t e]))]
        [#t (error "can't fix non qq format")]))

(define (get_vars e)
  (cond [(true? e) null]
        [(false? e) null]
        [(empty? e) null]
        [(zz? e) null]
        [(qq? e) null]
        [(s? e) null]
        [(valof? e) (cons (valof-s e) null)]
        [(..? e) (append (get_vars (..-e1 e)) (get_vars (..-e2 e)))]
        [(if-then-else? e) (append (get_vars (if-then-else-condition e)) (get_vars (if-then-else-e1 e)) (get_vars (if-then-else-e2 e)))]
        [(is-zz?? e) null]
        [(is-qq?? e) null]
        [(is-bool?? e) null]
        [(is-seq?? e) (get_vars is-seq?-e1 e)]
        [(is-proper-seq?? e) (get_vars is-proper-seq?-e1 e)]
        [(is-empty?? e) null]
        [(is-set?? e) null]
        [(add? e) (append (get_vars (add-e1 e)) (get_vars (add-e2 e)))]
        [(mul? e) (append (get_vars (mul-e1 e)) (get_vars (mul-e2 e)))]
        [(leq?? e) (append (get_vars (leq?-e1 e)) (get_vars (leq?-e2 e)))]
        [(rounding? e) null]
        [(=?? e) (append (get_vars (=?-e1 e)) (get_vars (=?-e2 e)))]
        [(left? e) (get_vars e)]
        [(right? e) (get_vars e)]
        [(~? e) (get_vars e)]
        [(any?? e) (get_vars e)]
        [(all?? e) (get_vars e)]
        [(vars? e) null]
        [(fun? e) (get_vars (fun-body e))]
        [(proc? e) (get_vars (proc-body e))]
        [(call? e) (get_vars (call-e e))]))

(define (rm_duplicates vars l acc)
  (if (or (null? vars) (null? l))
      acc
      (let ([ans (assoc (car vars) acc)])
        (if ans
            (rm_duplicates (cdr vars) l acc)
            (let ([val (assoc (car vars) l)])
              (if val
                  (rm_duplicates (cdr vars) (remove* (list val) l) (append acc (list val)))
                  (rm_duplicates (cdr vars) l acc)))))))

(define (rm_basic_duplicates l acc)
  (if (null? l)
      acc
      (if (member (car l) acc)
          (rm_basic_duplicates (cdr l) acc)
          (rm_basic_duplicates (cdr l) (append acc (list (car l)))))))
      

; (trace rm_duplicates)

(define (rm_env vs env)
  (if (null? vs)
      env
      (rm_env (cdr vs) (filter (lambda (arg) (not (equal? (car arg) (car vs)))) env))))

; (filter (lambda (arg) (not (equal? (car arg) "a"))) (list (cons "a" 5) (cons "a" 5) (cons "b" 5) (cons "c" 5)))
      
        
; Type checking functions.
(define (is-zz-fun e1 env)
  (let ([a (fri e1 env)])
    (if (zz? a)
        (true)
        (false))))

(define (is-qq-fun e1 env)
  (let ([a (fri e1 env)])
    (if (qq? a)
        (true)
        (false))))

(define (is-bool-fun e1 env)
  (let ([a (fri e1 env)])
    (if (or (true? a) (false? a))
        (true)
        (false))))

(define (is-seq-fun e1 env)
  (let ([a (fri e1 env)])
    (if (..? a)
        (true)
        (false))))

(define (is-proper-seq-fun e1 env)
  (let ([a (fri e1 env)])
    (if (..? a)
        (if (..? (..-e2 a))
            (is-proper-seq-fun (..-e2 a) env)
            (if (empty? (..-e2 a))
                (true)
                (false)))
        (false))))

(define (is-empty-fun e1 env)
  (let ([a (fri e1 env)])
    (if (empty? a)
        (true)
        (false))))

(define (is-set-fun e1 env)
  (let ([a (fri e1 env)])
    (if (set? a)
        (true)
        (false))))

;;;;; Operation logic functions. ;;;;;

; If then else logic.
(define (if_the_else_logic e env)
  (let ([cnd (fri (if-then-else-condition e) env)])
    (cond [(true? cnd) (fri (if-then-else-e1 e) env)]
          [(false? cnd) (fri (if-then-else-e2 e) env)]
          [#t (error "if-then-else condition invalid")])))

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
      (if (empty? z1)
          z2
          (.. z1 z2))
      (.. (..-e1 z1) (join (..-e2 z1) z2))))

(define (add_logic e1 e2 env)
  (let ([a (fri e1 env)]
        [b (fri e2 env)])
    (cond [(and (zz? a)(zz? b)) (zz (+ (zz-n a) (zz-n b)))]
          [(and (false? a) (false? b)) (false)]
          [(and (true? a) (false? b)) (true)]
          [(and (false? a) (true? b)) (true)]
          [(and (true? a) (true? b)) (true)]
          [(and (qq? a) (qq? b)) (letrec ([imen (* (zz-n (qq-e2 a)) (zz-n (qq-e2 b)))]
                                          [stev (+ (* (zz-n (qq-e1 a)) (zz-n (qq-e2 b))) (* (zz-n (qq-e1 b)) (zz-n (qq-e2 a))))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (qq? a) (zz? b)) (letrec ([imen (zz-n (qq-e2 a))]
                                          [stev (+ (zz-n (qq-e1 a)) (* (zz-n (qq-e2 a)) (zz-n b)))]
                                          [sht (shorten stev imen)]) (qq_format  (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (zz? a) (qq? b)) (letrec ([imen (zz-n (qq-e2 b))]
                                          [stev (+ (zz-n (qq-e1 b)) (* (zz-n (qq-e2 b)) (zz-n a)))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (..? a) (..? b)) (join a b)]
          [(and (s? a) (s? b)) (s (set-union (s-es a) (s-es b)))]
          [(and (empty? a) (empty? b)) (empty)]
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
      (cons (.. e (car l)) (make_pairs e (cdr l)))))

(define (mul_logic e1 e2 env)
  (let ([a (fri e1 env)]
        [b (fri e2 env)])
    (cond [(and (zz? a)(zz? b)) (zz (* (zz-n a) (zz-n b)))]
          [(and (false? a) (false? b)) (false)]
          [(and (true? a) (false? b)) (false)]
          [(and (false? a) (true? b)) (false)]
          [(and (true? a) (true? b)) (true)]
          [(and (qq? a) (qq? b)) (letrec ([imen (* (zz-n (qq-e2 a)) (zz-n (qq-e2 b)))]
                                          [stev (* (zz-n (qq-e1 a)) (zz-n (qq-e1 b)))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (qq? a) (zz? b)) (letrec ([imen (* (zz-n (qq-e2 a)) (zz-n b))]
                                          [stev (* (zz-n (qq-e1 a)) (zz-n b))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (zz? a) (qq? b)) (letrec ([imen (* (zz-n (qq-e2 b)) (zz-n a))]
                                          [stev (* (zz-n (qq-e1 b)) (zz-n a))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (s? a) (s? b)) (s (cartps (s-es a) (s-es b)))]
          [(and (empty? a) (empty? b)) (empty)]
          [#t (error "mul operation not supported")])))

; Leq logic.
(define (zap_len zap)
  (if (or (empty? zap) (not (..? zap)))
      1
      (+ 1 (zap_len (..-e2 zap)))))

(define (leq_logic e1 e2 env)
  (let ([a (fri e1 env)]
        [b (fri e2 env)])
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
          [(and (..? a) (..? b)) (if (<= (zap_len a) (zap_len b))
                                     (true)
                                     (false))]
          [(and (s? a) (s? b)) (if (subset? (s-es a) (s-es b))
                                   (true)
                                   (false))]
          [#t (error "leq? operation not supported")])))

; Rounding logic.
(define (rounding_logic e1 env)
  (let ([a (fri e1 env)])
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
                [#t #f]))))
          
(define (eq_logic e1 e2 env)
  (let ([a (fri e1 env)]
        [b (fri e2 env)])
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
          [(and (..? a) (..? b)) (if (zap_eq a b)
                                     (true)
                                     (false))]
          [(and (s? a) (s? b)) (if (equal? (s-es a) (s-es b))
                                   (true)
                                   (false))]
          [#t (false)])))
          
; (.. (zz 1) (.. (zz 2) (.. (zz 3) (zz 4))))

; Ecstraction loic.
(define (left_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(qq? a) (qq-e1 a)]
          [(..? a) (..-e1 a)]
          [(s? a) (set-first (s-es a))]
          [#t (error "left not supported")])))

(define (right_logic e1 env)
  (let ([a (fri e1 env)])
    (begin
      (displayln a)
    (cond [(qq? a) (qq-e2 a)]
          [(..? a) (..-e2 a)]
          [(s? a) (set-rest (s-es a))]
          [#t a]))))

; Neg logic.
(define (neg_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(zz? a) (zz (- 0 (zz-n a)))]
          [(true? a) (false)]
          [(false? a) (true)]
          [(qq? a) (qq_format (qq (zz (- 0 (zz-n (qq-e1 a)))) (qq-e2 a)))]
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
      
(define (all_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(s? a) (if (set-member? (s-es a) (false))
                      (false)
                      (true))]
          [(..? a) (if (all_zap a)
                       (true)
                       (false))]
          [#t (error "all not supported")])))

(define (any_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(s? a) (if (any_l (set->list (s-es a)))
                      (true)
                      (false))]
          [(..? a) (if (any_zap a)
                       (true)
                       (false))]
          [#t (error "any not supported")])))

(define (vars_logic e env)
  (if (list? (vars-s e))
      (fri (vars-e2 e) (fill_env (vars-s e) (vars-e1 e) env))
      (begin
        (set! env (append env (cons (cons (vars-s e) (fri (vars-e1 e) env)) null)))
        (fri (vars-e2 e) env))))

(define (valof_logic e env)
  (let ([ans (assoc (valof-s e) (reverse env))])
    (if ans
        (cdr ans)
        (error "var not in env"))))

;;;;; Functions. ;;;;;
(define (call_logic e env)
  (let ([o (fri (call-e e) env)])
    (cond [(closure? o)
               (fri (fun-body (closure-f o)) (let ([n_env (cons (cons (fun-name (closure-f o)) (closure-f o)) (closure-env o))])
                                               (fill_env (fun-farg (closure-f o)) (call-args e) n_env)))]
          [(proc? o) (let ([n_env (cons (cons (proc-name o) o) env)]) (fri (proc-body o) env))]
          [(fun? o) (call_logic (call o (call-args e)) env)] ; Valof "f" vrne (fun ...) ne pa (closure ...)
          [(error "fun call not correct")])))

;;;;; Macros. ;;;;;
(define (numerator e1)
  (left e1))

(define (denumerator e1)
  (right e1))

(define (gt? e1 e2)
  (~ (leq? e1 e2)))

(define (inv e1)
  (zz -1)) 

(define (mapping f seq)
  (zz -1))

(define (filtering f seq)
  (zz -1))

(define (folding f init seq)
  (if-then-else (is-empty? seq)
                init
                (if-then-else (is-seq? seq)
                              (if-then-else (is-empty? (right seq))
                                            (call f (list init (left seq)))
                                            (call f (list (left seq) (folding f init (right seq)))))
                              (zz -1))))
                              
;;;;; Main interpreter function. ;;;;;

(define (fill_env s e1 env)
  (if (null? s)
      env
      (begin
        (set! env (append env (cons (cons (car s) (fri (car e1) env)) null)))
        (fill_env (cdr s) (cdr e1) env))))

(define (fri e env)
  (cond [(true? e) e]
        [(false? e) e]
        [(zz? e) (if (integer? (zz-n e))
                     e
                     (error "zz mut have int value"))]
        [(qq? e) (let ([sht (shorten (zz-n (qq-e1 e)) (zz-n (qq-e2 e)))])
                       (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
        [(empty? e) e]
        [(..? e) (.. (fri (..-e1 e) env) (fri (..-e2 e) env))]
        [(s? e) e]
        [(if-then-else? e) (if_the_else_logic e env)]
        [(is-zz?? e) (is-zz-fun (is-zz?-e1 e) env)]
        [(is-qq?? e) (is-qq-fun (is-qq?-e1 e) env)]
        [(is-bool?? e) (is-bool-fun (is-bool?-e1 e) env)]
        [(is-seq?? e) (is-seq-fun (is-seq?-e1 e) env)]
        [(is-proper-seq?? e) (is-proper-seq-fun (is-proper-seq?-e1 e) env)]
        [(is-empty?? e) (is-empty-fun (is-empty?-e1 e) env)]
        [(is-set?? e) (is-set-fun (is-set?-e1 e) env)]
        [(add? e) (add_logic (add-e1 e) (add-e2 e) env)]
        [(mul? e) (mul_logic (mul-e1 e) (mul-e2 e) env)]
        [(leq?? e) (leq_logic (leq?-e1 e) (leq?-e2 e) env)]
        [(rounding? e) (rounding_logic (rounding-e1 e) env)]
        [(=?? e) (eq_logic (=?-e1 e) (=?-e2 e) env)]
        [(left? e) (left_logic (left-e1 e) env)]
        [(right? e) (right_logic (right-e1 e) env)]
        [(~? e) (neg_logic (~-e1 e) env)]
        [(all?? e) (all_logic (all?-e1 e) env)]
        [(any?? e) (any_logic (any?-e1 e) env)]
        [(vars? e) (vars_logic e env)]
        [(valof? e) (valof_logic e env)]
        [(proc? e) e]
        [(call? e) (call_logic e env)]
        [(fun? e) (closure (rm_duplicates (rm_basic_duplicates (get_vars (fun-body e)) null) (reverse env) null) e)]
        [#t (error "expression not supported by FR")]))

;;;;; Tests. ;;;;;
; (fri (vars "a" (zz 1) (call (fun "sestej" null (add (valof "a") (zz 2))) null)) null)
; (fri (vars "a" (zz 1) (call (proc "sestej" (add (valof "a") (zz 2))) null)) null)
; (fri (if-then-else (false) (zz 1) (zz 2)) null)
; (fri (vars (list "a" "b" "c") (list (add (zz 1) (zz 2)) (mul (zz 1) (zz 7)) (zz 4)) (valof "b")) null)
; (fri (call (fun "f" (list "a" "b") (add (valof "a") (valof "b"))) (list (zz 1) (zz 2))) null)
; (fri (call (fun "f" (list "a" "b") (add (valof "a") (valof "b"))) (list (mul (zz 5) (zz 6)) (add (zz 2) (zz 5)))) null)

; (fri (call (fun "f" (list "n") (if-then-else (=? (valof "n") (zz 0))
;                                              (zz 1)
;                                              (mul (valof "n") (call (valof "f") (list (add (valof "n") (zz -1))))) )) (list (zz 5)))  null)

; (folding (lambda (acc x) acc + x) 0 (empty))

; (trace fri)
; (trace fill_env)
; (trace join)
; (trace get_vars)

; (fri (=? (zz 2) (qq (zz 4) (zz 2))) null)

; (fri (folding (fun "" (list "acc" "z") (add (valof "acc") (valof "z"))) (zz 0) (.. (zz 2) (empty))) null)

; (fri (right (.. (zz 1) (empty))) null)
; (fri (is-empty? (right (.. (zz 1) (empty)))) null)
; (fri (is-empty? (empty)) null)
; (fri (folding (fun "" (list "acc" "z") (add (valof "acc") (valof "z"))) (zz 0) (.. (zz 1) (.. (zz 2) (empty)))) null)
; (folding (fun "f" (list "acc" "x") (add (valof "acc") (valof "x"))) (zz 0) (right (.. (zz 1) (.. (zz 2) (empty)))))