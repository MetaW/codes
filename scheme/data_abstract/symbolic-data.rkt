#lang racket


;使用symbolic
(define aa 'asdfe)
(define bb '(+ as 234 (77hj)))

(define cc `(,aa + nimk))

(quote 'qwsws)
;(quote 'exp) = 'exp


;函数eq?, equal?

;eq?只能判断两个symbol/atom是否相等,无法判断list
(eq? 123 123)
(eq? aa 'asdfe)
(eq? 'azsx 'azsss)

;用equal?判断symbol/atom或symbol/atom的list
(equal? 123 123)
(equal? 'asdsd 'asdsd)
(equal? (list 123 12) (list 123 12))
(equal? '(qas 234) '(qas 234))






;符号求导
;------------------------------------------------------
;只针对加法和乘法的表达式

(define (variable? exp) (symbol? exp))

(define (same-var? exp var) (eq? exp var))

(define (sum? exp)
	(eq? (car exp) '+))

(define (make-sum exp1 exp2)
	`(+ ,exp1 ,exp2))

(define (fstsum exp)
	(cadr exp))

(define (sndsum exp)
	(caddr exp))

(define (product? exp)
	(eq? (car exp) '*))

(define (make-prod exp1 exp2)
	`(* ,exp1 ,exp2))

(define (fstprod exp)
	(cadr exp))

(define (sndprod exp)
	(caddr exp))



(define (derive exp var)
	(cond	((number? exp) 0)
			((variable? exp) 
				(if (same-var? exp var) 1 0))
			((sum? exp) 
				(make-sum (derive (fstsum exp) var)
						  (derive (sndsum exp) var)))
			((product? exp)
				(make-sum (make-prod (derive (fstprod exp) var)
									 (sndprod exp))
						  (make-prod (fstprod exp)
						  			 (derive (sndprod exp) var))))
			(else (error "unknown expression!"))))


;(derive '(+ x 1) '1) 
;==> '(+ 1 0)





;集合的表示
;------------------------------------------------------









