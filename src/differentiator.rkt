#lang racket
(provide deriv simplify
         ;; Expression predicates
         variable? same-variable? sum? product? power?
         ;; Selectors
         addend augend multiplier multiplicand base exponent
         ;; Constructors
         make-sum make-product make-power)

;;; Expression predicates
(define (variable? e) (symbol? e))
(define (same-variable? v1 v2) (and (variable? v1) (variable? v2) (eq? v1 v2)))
(define (sum? e) (and (pair? e) (eq? (car e) '+)))
(define (product? e) (and (pair? e) (eq? (car e) '*)))
(define (power? e) (and (pair? e) (eq? (car e) '**)))
(define (trig? e) (and (pair? e) (memq (car e) '(sin cos tan))))

;;; Selectors
(define (addend e) (cadr e))
(define (augend e) (caddr e))
(define (multiplier e) (cadr e))
(define (multiplicand e) (caddr e))
(define (base e) (cadr e))
(define (exponent e) (caddr e))

;;; Constructors with simplification
(define (make-sum a1 a2)
  (cond
    [(and (number? a1) (number? a2)) (+ a1 a2)]
    [(and (number? a1) (= a1 0)) a2]
    [(and (number? a2) (= a2 0)) a1]
    [(and (number? a1) (number? a2)) (+ a1 a2)]
    [(and (sum? a1) (sum? a2))
     ; Flatten nested sums
     (list '+ (cadr a1) (caddr a1) (cadr a2) (caddr a2))]
    [(sum? a1)
     ; Check if a2 can be combined with last term of a1
     (let loop ((terms (cdr a1)) (acc '()))
       (if (null? (cdr terms))
           (append (reverse (cons a2 acc)) '())
           (loop (cdr terms) (cons (car terms) acc))))]
    [else (list '+ a1 a2)]))

(define (make-product m1 m2)
  (cond
    [(and (number? m1) (number? m2)) (* m1 m2)]
    [(or (and (number? m1) (= m1 0)) (and (number? m2) (= m2 0))) 0]
    [(and (number? m1) (= m1 1)) m2]
    [(and (number? m2) (= m2 1)) m1]
    [(and (number? m1) (number? m2)) (* m1 m2)]
    [(and (product? m1) (product? m2))
     ; Flatten nested products
     (list '* (cadr m1) (caddr m1) (cadr m2) (caddr m2))]
    [else (list '* m1 m2)]))

(define (make-power base exp)
  (cond
    [(and (number? exp) (= exp 0)) 1]
    [(and (number? exp) (= exp 1)) base]
    [(and (number? base) (number? exp)) (expt base exp)]
    [else (list '** base exp)]))

;;; Helper function to check if expression contains variable
(define (contains-variable? expr var)
  (cond
    [(number? expr) #f]
    [(variable? expr) (same-variable? expr var)]
    [(pair? expr) (or (contains-variable? (cadr expr) var)
                      (and (caddr expr) (contains-variable? (caddr expr) var)))]
    [else #f]))

;;; Main differentiation function
(define (deriv expr var)
  (cond
    [(number? expr) 0]
    [(variable? expr) (if (same-variable? expr var) 1 0)]
    [(sum? expr) 
     (make-sum (deriv (addend expr) var)
               (deriv (augend expr) var))]
    [(product? expr)
     (let ((u (multiplier expr))
           (v (multiplicand expr)))
       (make-sum
        (make-product (deriv u var) v)
        (make-product u (deriv v var))))]
    [(power? expr)
     (let ((u (base expr))
           (n (exponent expr)))
       (if (number? n)
           (make-product
            n
            (make-product
             (deriv u var)
             (make-power u (- n 1))))
           (error "Power rule requires numeric exponent")))]
    [(trig? expr)
     (let ((u (cadr expr))
           (du (deriv u var)))
       (if (contains-variable? u var)
           (case (car expr)
             [(sin) (make-product (make-trig 'cos u) du)]
             [(cos) (make-product (make-product -1 (make-trig 'sin u)) du)]
             [(tan) (make-product (make-power (make-trig 'sec u) 2) du)]
             [else (error "Unknown trig function" (car expr))])
           ; If argument doesn't contain variable, derivative is 0
           0))]
    [else (error "Unknown expression type" expr)]))

;;; Helper to create trig function expressions
(define (make-trig func arg)
  (list func arg))

;;; Simplification
(define (simplify expr)
  (cond
    [(number? expr) expr]
    [(variable? expr) expr]
    [(sum? expr)
     (let ((simple-addend (simplify (addend expr)))
           (simple-augend (simplify (augend expr))))
       (cond
         [(and (number? simple-addend) (= simple-addend 0)) simple-augend]
         [(and (number? simple-augend) (= simple-augend 0)) simple-addend]
         [(and (number? simple-addend) (number? simple-augend)) 
          (+ simple-addend simple-augend)]
         [(and (number? simple-addend) (sum? simple-augend))
          ; Distribute constant over sum: c + (a + b) -> (c + a) + b
          (make-sum (make-sum simple-addend (addend simple-augend))
                   (augend simple-augend))]
         [else (make-sum simple-addend simple-augend)]))]
    [(product? expr)
     (let ((simple-multiplier (simplify (multiplier expr)))
           (simple-multiplicand (simplify (multiplicand expr))))
       (cond
         [(or (and (number? simple-multiplier) (= simple-multiplier 0))
              (and (number? simple-multiplicand) (= simple-multiplicand 0))) 0]
         [(and (number? simple-multiplier) (= simple-multiplier 1)) 
          simple-multiplicand]
         [(and (number? simple-multiplicand) (= simple-multiplicand 1)) 
          simple-multiplier]
         [(and (number? simple-multiplier) (number? simple-multiplicand))
          (* simple-multiplier simple-multiplicand)]
         [(and (number? simple-multiplier) (product? simple-multiplicand))
          ; Distribute constant over product: c * (a * b) -> (c * a) * b
          (make-product (make-product simple-multiplier (multiplier simple-multiplicand))
                       (multiplicand simple-multiplicand))]
         [else (make-product simple-multiplier simple-multiplicand)]))]
    [(power? expr)
     (let ((simple-base (simplify (base expr)))
           (simple-exp (simplify (exponent expr))))
       (cond
         [(and (number? simple-exp) (= simple-exp 0)) 1]
         [(and (number? simple-exp) (= simple-exp 1)) simple-base]
         [(and (number? simple-base) (number? simple-exp)) 
          (expt simple-base simple-exp)]
         [else (make-power simple-base simple-exp)]))]
    [(trig? expr)
     (let ((simple-arg (simplify (cadr expr))))
       (list (car expr) simple-arg))]
    [else expr]))

;;; Additional simplification rules for derived expressions
(define (simplify-derivative expr)
  (let ((simplified (simplify expr)))
    ; Additional rules for common derivative patterns
    (cond
      [(and (product? simplified)
            (number? (multiplier simplified))
            (= (multiplier simplified) 1))
       (multiplicand simplified)]
      [(and (sum? simplified)
            (number? (addend simplified))
            (= (addend simplified) 0))
       (augend simplified)]
      [(and (sum? simplified)
            (number? (augend simplified))
            (= (augend simplified) 0))
       (addend simplified)]
      [else simplified])))

;;; Convenience function for getting simplified derivatives
(define (deriv-simplified expr var)
  (simplify-derivative (deriv expr var)))

;;; Tests
(module+ test
  (require rackunit)
  
  ; Basic derivative tests
  (check-equal? (deriv 5 'x) 0)
  (check-equal? (deriv 'x 'x) 1)
  (check-equal? (deriv 'y 'x) 0)
  
  ; Sum rule
  (check-equal? (deriv '(+ x 3) 'x) '(+ 1 0))
  (check-equal? (simplify (deriv '(+ x 3) 'x)) 1)
  
  ; Product rule
  (check-equal? (deriv '(* x x) 'x) '(+ (* 1 x) (* x 1)))
  (check-equal? (simplify (deriv '(* x x) 'x)) '(* 2 x))
  
  ; Power rule
  (check-equal? (deriv '(** x 3) 'x) '(* 3 (* 1 (** x 2))))
  (check-equal? (simplify (deriv '(** x 3) 'x)) '(* 3 (** x 2)))
  
  ; Trigonometric functions
  (check-equal? (deriv '(sin x) 'x) '(* (cos x) 1))
  (check-equal? (simplify (deriv '(sin x) 'x)) '(cos x))
  
  (check-equal? (deriv '(cos x) 'x) '(* (* -1 (sin x)) 1))
  (check-equal? (simplify (deriv '(cos x) 'x)) '(* -1 (sin x)))
  
  (check-equal? (deriv '(tan x) 'x) '(* (** (sec x) 2) 1))
  (check-equal? (simplify (deriv '(tan x) 'x)) '(** (sec x) 2))
  
  ; Chain rule with trig
  (check-equal? (deriv '(sin (* 2 x)) 'x) '(* (cos (* 2 x)) (* 0 x (* 2 1))))
  (check-equal? (simplify (deriv '(sin (* 2 x)) 'x)) '(* (cos (* 2 x)) 2))
  
  ; Test expressions from assignment
  (check-equal? 
   (simplify (deriv '(+ (* 7 (^ x 2)) (* 4 x) 5) 'x))
   '(+ (* 7 (* 2 x)) 4))
  
  (check-equal? 
   (simplify (deriv '(^ x 2) 'x))
   '(* 2 x))
  
  (check-equal? 
   (simplify (deriv '(* 3 (^ x 2)) 'x))
   '(* 3 (* 2 x)))
  
  (check-equal? 
   (simplify (deriv '(cos x) 'x))
   '(* -1 (sin x)))
  
  (check-equal? 
   (simplify (deriv '(sin x) 'x))
   '(cos x))
  
  (check-equal? 
   (simplify (deriv '(tan (* 3 x)) 'x))
   '(* (** (sec (* 3 x)) 2) 3)))