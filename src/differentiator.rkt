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
;; Support both ^ and ** for power expressions
(define (power? e)   (and (pair? e) (or (eq? (car e) '**) (eq? (car e) '^))))
;; Trigonometric predicates
(define (sin? e)     (and (pair? e) (eq? (car e) 'sin)))
(define (cos? e)     (and (pair? e) (eq? (car e) 'cos)))
(define (tan? e)     (and (pair? e) (eq? (car e) 'tan)))

;;; ================================================================
;;; Selectors
;;; ================================================================

(define (addend e)      (cadr e))
(define (augend e)      (caddr e))
(define (multiplier e)  (cadr e))
(define (multiplicand e)(caddr e))
(define (base e)        (cadr e))   ; base of a power expression
(define (exponent e)    (caddr e))  ; exponent of a power expression
(define (trig-arg e)    (cadr e))   ; argument of a trig function

;;; ================================================================
;;; Smart constructors with algebraic simplification
;;; ================================================================

;; make-sum: construct (+ a1 a2) with simplification
(define (make-sum a1 a2)
  (cond
    [(and (number? a1) (number? a2)) (+ a1 a2)]   ; constant folding
    [(and (number? a1) (= a1 0)) a2]               ; 0 + x = x
    [(and (number? a2) (= a2 0)) a1]               ; x + 0 = x
    [else (list '+ a1 a2)]))

;; make-product: construct (* m1 m2) with simplification
(define (make-product m1 m2)
  (cond
    [(and (number? m1) (number? m2)) (* m1 m2)]    ; constant folding
    [(and (number? m1) (= m1 0)) 0]                ; 0 * x = 0
    [(and (number? m2) (= m2 0)) 0]                ; x * 0 = 0
    [(and (number? m1) (= m1 1)) m2]               ; 1 * x = x
    [(and (number? m2) (= m2 1)) m1]               ; x * 1 = x
    [else (list '* m1 m2)]))

;; make-power: construct (^ base exp) with simplification
(define (make-power b e)
  (cond
    [(and (number? e) (= e 0)) 1]                  ; x^0 = 1
    [(and (number? e) (= e 1)) b]                  ; x^1 = x
    [(and (number? b) (number? e)) (expt b e)]     ; constant folding
    [else (list '^ b e)]))

;; make-neg: negate an expression
(define (make-neg e)
  (make-product -1 e))

;;; ================================================================
;;; Simplification pass
;;; ================================================================

;; Full recursive simplification
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
     (make-power (simplify (base expr))
                 (simplify (exponent expr)))]
    ;; Trig: recurse into argument
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
     (let ([u  (multiplier expr)]
           [v  (multiplicand expr)])
       (make-sum (make-product (deriv u var) v)
                 (make-product u (deriv v var))))]

    ;; Power rule with chain rule: d/dx[u^n] = n * u^(n-1) * u'
    [(power? expr)
     (let ([u (base expr)]
           [n (exponent expr)])
       (make-product (make-product n (make-power u (make-sum n -1)))
                     (deriv u var)))]

    ;; d/dx[sin(u)] = cos(u) * u'
    [(sin? expr)
     (let ([u (trig-arg expr)])
       (make-product (list 'cos u)
                     (deriv u var)))]

    ;; d/dx[cos(u)] = -sin(u) * u'
    [(cos? expr)
     (let ([u (trig-arg expr)])
       (make-product (make-neg (list 'sin u))
                     (deriv u var)))]

    ;; d/dx[tan(u)] = sec^2(u) * u'  represented as (^ (cos u) -2) * u'
    ;; sec^2(u) = 1/cos^2(u) = (cos u)^-2
    [(tan? expr)
     (let ([u (trig-arg expr)])
       (make-product (make-power (list 'cos u) -2)
                     (deriv u var)))]

    [else (error "Unknown expression type" expr)]))

;;; ================================================================
;;; Tests
;;; ================================================================

(module+ test
  (require rackunit)

  ;; --- Basic derivatives ---
  (check-equal? (deriv 5 'x) 0)
  (check-equal? (deriv 'x 'x) 1)
  (check-equal? (deriv 'y 'x) 0)

  ;; --- Sum rule ---
  (check-equal? (deriv '(+ x 3) 'x) 1)       ; 1 + 0 = 1
  (check-equal? (deriv '(+ x y) 'x) 1)       ; 1 + 0 = 1

  ;; --- Product rule ---
  ;; d/dx[3x] = 3
  (check-equal? (deriv '(* 3 x) 'x) 3)
  ;; d/dx[x*x] = x + x = 2x  (simplified via make-sum/make-product)
  (check-equal? (deriv '(* x x) 'x) '(+ x x))

  ;; --- Power rule ---
  ;; d/dx[x^2] = 2x
  (check-equal? (deriv '(^ x 2) 'x) '(* 2 x))
  ;; d/dx[x^3] = 3x^2
  (check-equal? (deriv '(^ x 3) 'x) '(* (* 3 (^ x 2)) 1))

  ;; --- Trig ---
  ;; d/dx[sin(x)] = cos(x)
  (check-equal? (deriv '(sin x) 'x) '(cos x))
  ;; d/dx[cos(x)] = -sin(x)
  (check-equal? (deriv '(cos x) 'x) '(* -1 (sin x)))
  ;; d/dx[tan(x)] = sec^2(x) = (cos x)^-2
  (check-equal? (deriv '(tan x) 'x) '(^ (cos x) -2))

  ;; --- Chain rule ---
  ;; d/dx[sin(2x)] = cos(2x) * 2
  (check-equal? (deriv '(sin (* 2 x)) 'x) '(* (cos (* 2 x)) 2))
  ;; d/dx[tan(3x)] = (cos(3x))^-2 * 3
  (check-equal? (deriv '(tan (* 3 x)) 'x) '(* (^ (cos (* 3 x)) -2) 3))

  ;; --- Polynomial: 7x^2 + 4x + 5 ---
  ;; d/dx = 14x + 4
  (let ([poly '(+ (+ (* 7 (^ x 2)) (* 4 x)) 5)])
    (check-equal? (deriv poly 'x)
                  '(+ (+ (* 7 (* 2 x)) 4) 0)))

  ;; --- Simplify ---
  (check-equal? (simplify '(+ 0 x)) 'x)
  (check-equal? (simplify '(* 1 x)) 'x)
  (check-equal? (simplify '(* 0 x)) 0)
  (check-equal? (simplify '(+ 2 3)) 5))