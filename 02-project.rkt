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
        [(is-seq?? e) (get_vars (is-seq?-e1 e))]
        [(is-proper-seq?? e) (get_vars is-proper-seq?-e1 e)]
        [(is-empty?? e) null]
        [(is-set?? e) null]
        [(add? e) (append (get_vars (add-e1 e)) (get_vars (add-e2 e)))]
        [(mul? e) (append (get_vars (mul-e1 e)) (get_vars (mul-e2 e)))]
        [(leq?? e) (append (get_vars (leq?-e1 e)) (get_vars (leq?-e2 e)))]
        [(rounding? e) null]
        [(=?? e) (append (get_vars (=?-e1 e)) (get_vars (=?-e2 e)))]
        [(left? e) (get_vars (left-e1 e))]
        [(right? e) (get_vars (right-e1 e))]
        [(~? e) (get_vars (~-e1 e))]
        [(any?? e) (get_vars (any?-e1))]
        [(all?? e) (get_vars (all?-e1))]
        [(vars? e) null]
        [(fun? e) (append (fun-farg e) (get_vars (fun-body e)))]
        [(proc? e) (get_vars (proc-body e))]
        [(call? e) (append (get_vars (call-e e)) (sweep_args (call-args e) null))]
        [#t null]))

(define (sweep_args args acc)
  (if (null? args)
      acc
      (sweep_args (cdr args) (append acc (get_vars (car args))))))

(define (list-copy list)
  (if (null? list) '() (cons (car list) (list-copy (cdr list)))))

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

; (join (.. 1 (.. 2 (.. 3 (empty)))) (.. 4 (.. 5 (.. 6 7))))

(define (join z1 z2)
  (if (not (..? z1))
      (if (empty? z1)
          z2
          (join (.. z1 (empty)) z2))
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
          [(and (empty? a) (..? b)) (join a b)]
          [(and (..? a) (empty? b)) (join a b)]
          [(and (zz? a) (..? b)) (join a b)]
          [(and (..? a) (zz? b)) (join a b)]
          [(and (qq? a) (..? b)) (join a b)]
          [(and (..? a) (qq? b)) (join a b)]
          [(and (s? a) (..? b)) (join a b)]
          [(and (..? a) (s? b)) (join a b)]
          [(and (true? a) (..? b)) (join a b)]
          [(and (..? a) (true? b)) (join a b)]
          [(and (false? a) (..? b)) (join a b)]
          [(and (..? a) (false? b)) (join a b)]
          [(and (s? a) (s? b)) (s (set-union (s-es a) (s-es b)))]
          [(and (empty? a) (empty? b)) (empty)]
          [#t (error "add operation not supported")])))

; Mul logic.
(define (cartps s1 s2)
  (letrec ([l1 (set->list s1)]
           [l2 (set->list s2)])
    (list->set (map (lambda (x) (.. (car x) (car (cdr x)))) (cartesian-product l1 l2)))))

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
          [(and (qq? a) (zz? b)) (letrec ([imen (zz-n (qq-e2 a))]
                                          [stev (* (zz-n (qq-e1 a)) (zz-n b))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (zz? a) (qq? b)) (letrec ([imen (zz-n (qq-e2 b))]
                                          [stev (* (zz-n (qq-e1 b)) (zz-n a))]
                                          [sht (shorten stev imen)]) (qq_format (qq (zz (car sht)) (zz (cdr sht)))))]
          [(and (s? a) (s? b)) (s (cartps (s-es a) (s-es b)))]
          [(and (empty? a) (empty? b)) (empty)]
          [#t (error "mul operation not supported")])))

; Leq logic.
(define (zap_len zap)
  (cond [(empty? zap) 0]
        [(not (..? zap)) 1]
        [#t (+ 1 (zap_len (..-e2 zap)))]))

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
(define (eq_logic e1 e2 env)
  (let ([a (fri e1 env)]
        [b (fri e2 env)])
    (if (equal? a b)
        (true)
        (false))))

; Ecstraction loic.
(define (left_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(qq? a) (qq-e1 a)]
          [(..? a) (..-e1 a)]
          [(s? a) (set-first (s-es a))]
          [#t a])))

(define (right_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(qq? a) (qq-e2 a)]
          [(..? a) (..-e2 a)]
          [(s? a) (s (set-rest (s-es a)))]
          [#t a])))

; Neg logic.
(define (neg_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(zz? a) (zz (- (zz-n a)))]
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
      (and (not (equal? zap (false))) (not (equal? zap (empty))))))

(define (any_l l)
  (if (null? l)
      #f
      (or (not (equal? (car l) (false))) (any_l (cdr l)))))
      
(define (all_logic e1 env)
  (let ([a (fri e1 env)])
    (cond [(empty? a) (true)]
          [(s? a) (if (set-member? (s-es a) (false))
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
          [(empty? a) (false)]
          [#t (error "any not supported")])))

;;;;; Variables. ;;;;;
(define (fill_env s e1 env)
  (if (null? s)
      env
      (begin
        (set! env (append env (cons (cons (car s) (fri (car e1) env)) null)))
        (fill_env (cdr s) (cdr e1) env))))

; (fill_env (list "f") (list (fun "f" (list "x") (add (valof "x") (zz 2)))) null)

(define (vars_logic e env)
  (if (list? (vars-s e))
      (fri (vars-e2 e) (fill_env (vars-s e) (vars-e1 e) env))
      (begin
        (letrec ([val (fri (vars-e1 e) env)]
              [val2 (if (closure? val)
                           (closure-f val)
                           val)])
        (fri (vars-e2 e) (append env (list (cons (vars-s e) val2))))))))

(define (valof_logic e env)
  (let ([ans (assoc (valof-s e) (reverse env))])
    (if ans
        (cdr ans)
        (error (string-append "var not in env: " (valof-s e))))))

;;;;; Functions. ;;;;;
(define (fill_closure_env s e1 env cl_env)
  (if (null? s)
      (if (list? cl_env)
          cl_env
          (list cl_env))
      (let ([n_cl_env (append cl_env (list (cons (car s) (fri (car e1) env))))])
        (fill_closure_env (cdr s) (cdr e1) env n_cl_env))))

; (trace fill_closure_env)
; (fill_closure_env (list "a") (list (valof "seq")) (list (cons "seq" (zz 4))) null)
  
(define (call_logic e env)
  (let ([o (fri (call-e e) env)])
    (cond [(closure? o)
           (letrec ([vars (rm_basic_duplicates (append (get_vars (fun-body (closure-f o))) (sweep_args (call-args e) null)) null)]
                    [n_env1 (fill_closure_env (fun-farg (closure-f o)) (call-args e) env (closure-env o)) ]
                    [ans (assoc (fun-name (closure-f o)) n_env1)]
                    [n_env2 (if ans
                                n_env1
                                (append n_env1 (list (cons (fun-name (closure-f o)) (closure-f o)))))])
                 (fri (fun-body (closure-f o)) n_env2))]
          [(fun? o) (call_logic (call o (call-args e)) env)]
          [(proc? o) (let ([n_env (cons (cons (proc-name o) o) env)]) (fri (proc-body o) n_env))]
          [(error "fun call not correct")])))

; (fri (mapping (fun "f" (list "a") (mul (valof "a") (zz 2))) (.. (zz 1) (empty))) null)
; (fill_env (fun-farg (closure-f o)) (call-args e) n_env)

;;;;; Macros. ;;;;;
(define (numerator e1)
  (left e1))

(define (denominator e1)
  (right e1))

(define (gt? e1 e2)
  (~ (leq? e1 e2)))

(define (inv e1)
  (if-then-else (is-seq? e1)
                (call (fun "rev" (list "acc" "seq") (if-then-else (~ (is-seq? (valof "seq")))
                                                                  (if-then-else (is-empty? (valof "seq"))
                                                                                (valof "acc")
                                                                                (add (valof "seq") (valof "acc"))) ; Neprava zaporedja.
                                                                  (call (valof "rev") (list (add (.. (left (valof "seq")) (empty)) (valof "acc")) (right (valof "seq")))))) (list (empty) e1))
                (if-then-else (is-zz? e1)
                              (qq (zz 1) e1)
                              (qq (right e1) (left e1)))))

(define (mapping f seq)
  (call (fun "map" (list "f" "seq") (if-then-else (~ (is-seq? (valof "seq")))
                                                  (if-then-else (is-empty? (valof "seq"))
                                                                (empty)
                                                                (call (valof "f") (list (valof "seq"))))
                                                  (.. (call (valof "f") (list (left (valof "seq")))) (call (valof "map") (list (valof "f") (right (valof "seq"))))))) (list f seq)))

(define (filtering f seq)
  (call (fun "filter" (list "f" "seq") (if-then-else (~ (is-seq? (valof "seq")))
                                                  (if-then-else (is-empty? (valof "seq"))
                                                                (empty)
                                                                (if-then-else (call (valof "f") (list (valof "seq")))
                                                                              (valof "seq")
                                                                              (empty)))
                                                  (if-then-else (call (valof "f") (list (left (valof "seq"))))
                                                                (.. (left (valof "seq")) (call (valof "filter") (list (valof "f") (right (valof "seq")))))
                                                                (call (valof "filter") (list (valof "f") (right (valof "seq"))))))) (list f seq)))
                                             
(define (folding f init seq)
  (call (fun "fold" (list "f" "init" "seq") (if-then-else (~ (is-seq? (valof "seq")))
                                                          (if-then-else (is-empty? (valof "seq"))
                                                                        (valof "init")
                                                                        (call (valof "f") (list (valof "seq") (valof "init"))))
                                                          (call (valof "f") (list (call (valof "fold") (list (valof "f") (valof "init") (right (valof "seq")))) (left (valof "seq")))))) (list f init seq)))
                                                                                                                  
;;;;; Main interpreter function. ;;;;;
(define (fri e env)
  (cond [(true? e) e]
        [(false? e) e]
        [(zz? e) (if (integer? (zz-n e))
                     e
                     (error "zz mut have int value"))]
        [(qq? e) (letrec ([st (fri (qq-e1 e) env)]
                          [im (fri (qq-e2 e) env)]
                          [sht (shorten (zz-n st) (zz-n im))])
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
        [(fun? e) (closure (rm_duplicates (rm_basic_duplicates (get_vars (fun-body e)) null) (reverse (list-copy env)) null) e)]
        [#t (error "expression not supported by FR")]))

; (trace fri)

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
; (fri (=? (zz 2) (qq (zz 4) (zz 2))) null)

; (fri (folding (fun "" (list "acc" "z") (add (valof "acc") (valof "z"))) (zz 0) (.. (zz 2) (empty))) null)

; (fri (right (.. (zz 1) (empty))) null)
; (fri (is-empty? (right (.. (zz 1) (empty)))) null)
; (fri (is-empty? (empty)) null)
; (fri (folding (fun "" (list "acc" "z") (add (valof "acc") (valof "z"))) (zz 0) (.. (zz 1) (.. (zz 2) (empty)))) null)
; (folding (fun "f" (list "acc" "x") (add (valof "acc") (valof "x"))) (zz 0) (right (.. (zz 1) (.. (zz 2) (empty)))))

; (fri (mapping (fun "f" (list "a") (mul (valof "a") (zz 2))) (.. (zz 1) (empty))) null)
; (fri (filtering (fun "f" (list "a") (is-zz? (valof "a"))) (.. (zz 1) (.. (zz 2) (.. (qq (zz 2) (zz 4)) (empty))))) null)
; (fri (filtering (fun "f" (list "a") (is-zz? (valof "a"))) (.. (zz 1) (.. (zz 2) (.. (qq (zz 2) (zz 4)) (.. (.. (zz 5) (zz 6)) (empty)))))) null)
; (fri (folding (fun "" (list "acc" "x") (add (valof "acc") (valof "x"))) (zz 0) (.. (zz 1) (empty))) null)
; (fri (folding (fun "f" (list "acc" "x") (add (valof "acc") (valof "x"))) (zz 0) (.. (zz 1) (.. (zz 2) (.. (zz 3) (zz 4))))) null)
; (fri (inv (qq (zz 2) (zz 3))) null)
; (fri (inv (zz 3)) null)
; (fri (inv (.. (zz 3) (empty))) null)

; (define env2 (list (cons "a" (zz 5)) (cons "b" (zz 2)) (cons "c" (zz 3)) (cons "d" (zz 4)) (cons "g" (fun "f" (list "x" "z") (add (valof "x") (valof "z"))))))
; (define env3 (list (cons "a" (zz 5)) (cons "b" (zz 2)) (cons "c" (zz 3)) (cons "d" (zz 4)) (cons "g" (fun "g" (list "x") (add (valof "x") (zz 2))))))

; (fri (call (fun "f" (list "x") (add (zz 2) (valof "x"))) (list (valof "a"))) env2)
; (fri (call (fun "f" (list "x") (add (zz 2) (valof "x"))) (list (call (valof "g") (list (valof "a") (valof "b"))))) env2)
; (fri (call (proc "p" (add (valof "a") (zz 2))) null) null)

; (fri (call (fun "" null (inv (add (zz 2) (valof "a")))) null) (list (cons "a" (zz 5))))

; (define env5 (list (cons "f" (closure null (fun "f" (list "a") (mul (valof "a") (zz 2))))) (cons "seq" (zz 5))))
; (fri (call (valof "f") (list (valof "seq"))) env5)
