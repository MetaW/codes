#lang racket




; lazy evaluation
;----------------------------------------------------------
;we create lazy evaluation list or streams here

; (delay exp) ==> (lambda () exp)

; DO NOT define delay as a function because it will 
; eval its params before wraping into lambda, and lazy
; eval doesn't work.

(define (force obj)
	(obj))

;all right! 
;then we create the abstract of stream with the interface

; (mystream-cons a b) ==> (cons a (lambda () b))

; DO NOT define mystream-cons as a function, the reason is
; the same as delay.

(define (mystream-car s)
	(car s))

(define (mystream-cdr s)
	(force (cdr s)))



(define (mystream-map f s)
	(if (null? s)
		'()
		(cons (f (mystream-car s))
			  (lambda () (mystream-map f (mystream-cdr s))))))


(define (mystream-filter p s)
	(cond   [(null? s) '()]
			[(p (mystream-car s))
				(cons (mystream-car s)
					  (lambda () (mystream-filter p (mystream-cdr s))))]
			[else (mystream-filter p (mystream-cdr s))]))



(define (mystream-enum-interval st ed)
	(if (> st ed)
		'()
		(cons st 
			  (lambda () (mystream-enum-interval (+ st 1) ed)))))




;example: calculate the second odd number between 1000 and 1000000
(mystream-car (mystream-cdr (mystream-filter
		 								odd?
			    						(mystream-enum-interval 1000 1000000))))







;lazy evaluation with cacahe
;----------------------------------------------------------
; we define a memory function which can remember a lambda's
; value in the first calcu and give the value directlly later.

; we define a memo-fun and delay was replaced with (memo-fun (delay <exp>))

; (memo-fun (delay <exp>)) ==> (memo-fun (lambda () <exp>))

(define (memo-fun lambda-exp)
	(let ((already-run? false) (result false))
		 (lambda ()
		 	(if (= already-run? false)
		 		(begin  (set! already-run true)
		 				(set! result (lambda-exp))
		 				result)
		 		result))))

; then we can use "(memo-fun (lambda () <exp>))" to replace
; "(lambda () <exp>)"








;infinite stream
;---------------------------------------------------------

; example
(define (int-start-from n)
	(cons n (lambda () (int-start-from (+ n 1)))))


;now we use it to create a infinite prime number stream

(define (divisible? x y) (= (remainder x y) 0))

(define intfrom2 (int-start-from 2))

(define (sieve-stream s) 
	(cons 	(mystream-car s)
			(lambda () 
				(sieve-stream 
					(mystream-filter (lambda (x) (not (divisible? x (mystream-car s)))) 
								 	 (mystream-cdr s))))))

;now we get a prime stream:
(define prime-stream (sieve-stream intfrom2))

 





