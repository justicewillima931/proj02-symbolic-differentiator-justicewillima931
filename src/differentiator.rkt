#lang racket
(provide deriv simplify
         variable? same-variable? sum? product? power?
         addend augend multiplier multiplicand
         make-sum make-product)

;;; ================================================================
;;; 1. Expression Predicates
;;; ================================================================

(define (variable? e) (symbol? e))
(define (same-variable? v1 v2) (and (variable? v1) (variable? v2) (eq? v1 v2)))
(define (sum? e)     (and (pair? e) (eq? (car e) '+)))
(define (product? e) (and (pair? e) (eq? (car e) '*)))
(define (power? e)   (and (pair? e) (or (eq? (car e) '**) (eq? (car e) '^))))

;; Variant Specific Trig Predicates 
(define (sin? e)     [cite_start](and (pair? e) (eq? (car e) 'sin))) [cite: 1]
(define (cos? e)     [cite_start](and (pair? e) (eq? (car e) 'cos))) [cite: 1]
(define (tan? e)     [cite_start](and (pair? e) (eq? (car e) 'tan))) [cite: 1]

;;; ================================================================
;;; 2. Selectors
;;; ================================================================

(define (addend e)       (cadr e))
(define (augend e)       (caddr e))
(define (multiplier e)   (cadr e))
(define (multiplicand e) (caddr e))
(define (base e)         (cadr e))
(define (exponent e)     (caddr e))
(define (trig-arg e)     [cite_start](cadr e)) [cite: 1]

;;; ================================================================
;;; 3. Smart Constructors (Milestone 3 Simplification) 
;;; ================================================================

(define (make-sum a1 a2)
  (cond [(and (number? a1) [cite_start](number? a2)) (+ a1 a2)][cite: 1]; Constant folding 
        [cite_start][(equal? a1 0) a2][cite: 1]; 0 + x = x 
        [cite_start][(equal? a2 0) a1] [cite: 1]                      [cite_start]; x + 0 = x 
        [else (list '+ a1 a2)]))

(define (make-product m1 m2)
  (cond [(and (number? m1) [cite_start](number? m2)) (* m1 m2)][cite: 1]; Constant folding 
        [cite_start][(or (equal? m1 0) (equal? m2 0)) 0][cite: 1]; 0 * x = 0 
        [cite_start][(equal? m1 1) m2][cite: 1]; 1 * x = x 
        [cite_start][(equal? m2 1) m1] [cite: 1]                      [cite_start]; x * 1 = x 
        [else (list '* m1 m2)]))

(define (make-power b e)
  (cond [(equal? e 0) 1]                        ; x^0 = 1
        [(equal? e 1) b]                        ; x^1 = x
        [(and (number? b) (number? e)) (expt b e)]
        [else (list '^ b e)]))

;;; ================================================================
;;; 4. Main Differentiation Function 
;;; ================================================================

(define (deriv expr var)
  (cond
    [cite_start][(number? expr) 0] [cite: 1]
    [cite_start][(variable? expr) (if (same-variable? expr var) 1 0)] [cite: 1]
    
    ;; Sum Rule: d/dx[u + v] = du/dx + dv/dx 
    [(sum? expr) 
     (make-sum (deriv (addend expr) var)
               (deriv (augend expr) var))]
    
    ;; Product Rule: d/dx[u * v] = u'v + uv' 
    [(product? expr)
     (make-sum (make-product (deriv (multiplier expr) var)
                            (multiplicand expr))
               (make-product (multiplier expr)
                            (deriv (multiplicand expr) var)))]
    
    ;; Power Rule: d/dx[u^n] = n * u^(n-1) * u' 
    [(power? expr)
     (let ([u (base expr)]
           [n (exponent expr)])
       (make-product (make-product n (make-power u (make-sum n -1)))
                     (deriv u var)))]
    
    ;; Variant Trig Rules 
    [cite_start][(sin? expr) ; d/dx[sin(u)] = cos(u) * u' 
     (make-product (list 'cos (trig-arg expr))
                   (deriv (trig-arg expr) var))]
                   
    [cite_start][(cos? expr) ; d/dx[cos(u)] = -sin(u) * u' 
     (make-product (make-product -1 (list 'sin (trig-arg expr)))
                   (deriv (trig-arg expr) var))]
                   
    [cite_start][(tan? expr) ; d/dx[tan(u)] = sec^2(u) * u' 
     (make-product (make-power (list 'sec (trig-arg expr)) 2)
                   (deriv (trig-arg expr) var))]
                   
    [else (error "Unknown expression type" expr)]))

;;; ================================================================
;;; 5. Global Simplification Pass 
;;; ================================================================

(define (simplify expr)
  (cond [(number? expr) [cite_start]expr] [cite: 1]
        [cite_start][(variable? expr) expr] [cite: 1]
        [cite_start][(sum? expr) (make-sum (simplify (addend expr)) (simplify (augend expr)))] [cite: 1]
        [cite_start][(product? expr) (make-product (simplify (multiplier expr)) (simplify (multiplicand expr)))] [cite: 1]
        [cite_start][(power? expr) (make-power (simplify (base expr)) (simplify (exponent expr)))] [cite: 1]
        [cite_start][(pair? expr) (cons (car expr) (map simplify (cdr expr)))] [cite: 1]
        [else expr]))