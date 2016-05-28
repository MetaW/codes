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

(define (memo-fun f)
	())








