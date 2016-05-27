#lang racket

;we create lazy evaluation list or streams here

(define (delay exp)
	(lambda () exp))

(define (force obj)
	(obj))

;all right! 
;then we create the abstract of stream with the interface

(define (stream-cons a b)
	(cons a (delay b)))

(define (stream-car s)
	(car s))

(define (stream-cdr s)
	(force (cdr s)))



(define (stream-map f s)
	(if (null? s)
		'()
		(stream-cons (f (stream-car s))
					 (stream-map f (stream-cdr s)))))
(define (stream-filter p s)
	(cons   ((null? s) '())
			((p (stream-car s))
				(stream-cons (stream-car s)
							 (stream-filter p (stream-cdr s))))
			(else (stream-filter p (stream-cdr s)))))

(define (stream-enum-interval st ed)
	(if (> st ed)
		'()
		(stream-cons st 
					 (stream-enum-interval (+ st 1) ed))))












