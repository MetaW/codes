
;仅用过程实现cons,car,cdr

(define (mycons x y)
	(lambda (m) (m x y)))

(define (mycar p)
	(p (lambda (a b) a)))

(define (mycdr p)
	(p (lambda (a b) b)))


;任意个参数的函数
(define (same_parity x . li)
	(define (func a res)
		(if (null? res)	;;判断是否为()
			()
			(if (= (remainder (car res) 2) a)
				(cons (car res) (func a (cdr res)))
				(func a (cdr res)))))
	(if (= (remainder x 2) 0)
	 	(func 0 (cons x li))
	 	(func 1 (cons x li))))


;;;;;;;;;;;;;;;;;;;;;;;;sequence operaton!
;programming in sequence transforming

;generate a sequence

;使用map
(define (squire_list li)
	(map (lambda (x) (* x x)) li))


;使用filter
(filter odd? (list 1 2 3 4 5 6))


;accumulate
(fold + 0 (list 1 2 3 4))






