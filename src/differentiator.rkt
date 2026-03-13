#lang racket
(provide deriv simplify
         ;; Expression predicates
         variable? same-variable? sum? product? power?
         ;; Selectors
         addend augend multiplier multiplicand
         ;; Constructors
         make-sum make-product)

;;; ================================================================
;;; Expression predicates
;;; ================================================================

(define (variable? e) (symbol? e))
(define (same-variable? v1 v2) (and (variable? v1) (variable? v2) (eq? v1 v2)))
(define (sum? e)     (and (pair? e) (eq? (car e) '+)))
(define (product? e) (and (pair? e) (eq? (car e) '*)))
;; Accept both ^ and ** as power operators
(define (power? e)   (and (pair? e) (or (eq? (car e) '**) (eq? (car e) '^))))
;; Trigonometric predicates
(define (sin? e)     (and (pair? e) (eq? (car e) 'sin)))
(define (cos? e)     (and (pair? e) (eq? (car e) 'cos)))
(define (tan? e)     (and (pair? e) (eq? (car e) 'tan)))

;;; ================================================================
;;; Selectors
;;; ================================================================

(define (addend e) (cadr e))
;; augend: fold n-ary sums — (+ a b c) treated as (+ a (+ b c))
(define (augend e)
  (if (null? (cdddr e))
      (caddr e)
      (cons '+ (cddr e))))

(define (multiplier e) (cadr e))
;; multiplicand: fold n-ary products similarly
(define (multiplicand e)
  (if (null? (cdddr e))
      (caddr e)
      (cons '* (cddr e))))

(define (base e)     (cadr e))
(define (exponent e) (caddr e))
;; Preserve the original power operator symbol (^ or **)
(define (power-op e) (car e))
(define (trig-arg e) (cadr e))

;;; ================================================================
;;; Smart constructors with algebraic simplification
;;; ================================================================

(define (make-sum a1 a2)
  (cond
    [(and (number? a1) (number? a2)) (+ a1 a2)]   ; constant folding
    [(and (number? a1) (= a1 0)) a2]               ; 0 + x = x
    [(and (number? a2) (= a2 0)) a1]               ; x + 0 = x
    [else (list '+ a1 a2)]))

(define (make-product m1 m2)
  (cond
    [(and (number? m1) (number? m2)) (* m1 m2)]    ; constant folding
    [(and (number? m1) (= m1 0)) 0]                ; 0 * x = 0
    [(and (number? m2) (= m2 0)) 0]                ; x * 0 = 0
    [(and (number? m1) (= m1 1)) m2]               ; 1 * x = x
    [(and (number? m2) (= m2 1)) m1]               ; x * 1 = x
    [else (list '* m1 m2)]))

;; make-power: preserve the operator symbol used in the original expression
(define (make-power-with-op op expr-base expr-exp)
  (cond
    [(and (number? expr-exp) (= expr-exp 0)) 1]
    [(and (number? expr-exp) (= expr-exp 1)) expr-base]
    [(and (number? expr-base) (number? expr-exp)) (expt expr-base expr-exp)]
    [else (list op expr-base expr-exp)]))

;; Default make-power uses ** to match the test file convention
(define (make-power expr-base expr-exp)
  (make-power-with-op '** expr-base expr-exp))

(define (make-neg expr)
  (make-product -1 expr))

;;; ================================================================
;;; Simplification pass
;;; ================================================================

(define (simplify expr)
  (cond
    [(number? expr) expr]
    [(variable? expr) expr]
    [(sum? expr)
     (make-sum (simplify (addend expr))
               (simplify (augend expr)))]
    [(product? expr)
     (make-product (simplify (multiplier expr))
                   (simplify (multiplicand expr)))]
    [(power? expr)
     (make-power-with-op (power-op expr)
                         (simplify (base expr))
                         (simplify (exponent expr)))]
    [(or (sin? expr) (cos? expr) (tan? expr))
     (list (car expr) (simplify (trig-arg expr)))]
    [else expr]))

;;; ================================================================
;;; Main differentiation function
;;; ================================================================

(define (deriv expr var)
  (cond
    ;; d/dx[c] = 0
    [(number? expr) 0]

    ;; d/dx[x] = 1, d/dx[y] = 0
    [(variable? expr)
     (if (same-variable? expr var) 1 0)]

    ;; Sum rule: d/dx[u + v] = u' + v'
    [(sum? expr)
     (make-sum (deriv (addend expr) var)
               (deriv (augend expr) var))]

    ;; Product rule: d/dx[u * v] = u'v + uv'
    [(product? expr)
     (let ([expr-left  (multiplier expr)]
           [expr-right (multiplicand expr)])
       (make-sum (make-product (deriv expr-left var) expr-right)
                 (make-product expr-left (deriv expr-right var))))]

    ;; Power rule + chain rule: d/dx[u^n] = n * u^(n-1) * u'
    ;; Preserves original operator (^ or **)
    [(power? expr)
     (let ([op       (power-op expr)]
           [expr-base (base expr)]
           [expr-exp  (exponent expr)])
       (make-product
         (make-product expr-exp
                       (make-power-with-op op expr-base (make-sum expr-exp -1)))
         (deriv expr-base var)))]

    ;; d/dx[sin(u)] = cos(u) * u'
    [(sin? expr)
     (let ([expr-inner (trig-arg expr)])
       (make-product (list 'cos expr-inner)
                     (deriv expr-inner var)))]

    ;; d/dx[cos(u)] = -sin(u) * u'
    [(cos? expr)
     (let ([expr-inner (trig-arg expr)])
       (make-product (make-neg (list 'sin expr-inner))
                     (deriv expr-inner var)))]

    ;; d/dx[tan(u)] = sec^2(u) * u' = (cos u)^{-2} * u'
    [(tan? expr)
     (let ([expr-inner (trig-arg expr)])
       (make-product (make-power (list 'cos expr-inner) -2)
                     (deriv expr-inner var)))]

    [else (error "Unknown expression type" expr)]))

;;; ================================================================
;;; Tests matching the visible test suite exactly
;;; ================================================================

(module+ test
  (require rackunit)

  ;; Basic
  (check-equal? (deriv 5 'x) 0)
  (check-equal? (deriv 'x 'x) 1)
  (check-equal? (deriv 'y 'x) 0)

  ;; Sum: result is 1 (make-sum simplifies 1+0=1)
  (check-true (let ([r (deriv '(+ x 3) 'x)])
                (or (equal? r 1) (equal? r '(+ 1 0)))))

  ;; Product: d/dx[2x] = 2
  (check-true (let ([r (deriv '(* 2 x) 'x)])
                (or (equal? r 2)
                    (equal? r '(+ (* 2 1) (* 0 x)))
                    (equal? r '(+ (* 0 x) (* 2 1))))))

  ;; Power: d/dx[x**2] = (* 2 x) or (* 2 (** x 1))
  (check-true (let ([r (deriv '(** x 2) 'x)])
                (or (equal? r '(* 2 x))
                    (equal? r '(* 2 (** x 1))))))

  ;; Assignment test expressions
  ;; 7x^2 + 4x + 5 (3-arg sum)
  (check-equal? (deriv '(+ (* 7 (** x 2)) (* 4 x) 5) 'x) '(+ (* 14 x) 4))

  ;; cos(x) => (* -1 (sin x))
  (check-equal? (deriv '(cos x) 'x) '(* -1 (sin x)))

  ;; sin(x) => (cos x)
  (check-equal? (deriv '(sin x) 'x) '(cos x))

  ;; tan(3x) => (* (** (cos (* 3 x)) -2) 3)
  (check-equal? (deriv '(tan (* 3 x)) 'x)
                '(* (** (cos (* 3 x)) -2) 3))

  ;; Simplify
  (check-equal? (simplify '(+ 0 x)) 'x)
  (check-equal? (simplify '(* 1 x)) 'x)
  (check-equal? (simplify '(* 0 x)) 0)
  (check-equal? (simplify '(+ 2 3)) 5))
