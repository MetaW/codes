

(define left 100)

;use "set!" to change the value of left
(set! left 80)


;;;begin
;(begin exp1 exp2 exp3 ... expn) ==> value of expn.


;example
(define balance 100)

(define (withdrow x)
	(if (>= balance x)
		(begin (set! balance (- balance x))
			   balance)
		"insufficent money!"))











