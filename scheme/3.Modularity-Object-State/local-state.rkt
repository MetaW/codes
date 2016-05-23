#lang racket



;use set! to change the value of a variable
;-------------------------------------------------
(define left 100)

;use "set!" to change the value of left
(set! left 80)





; begin expression
;-------------------------------------------------
;(begin exp1 exp2 exp3 ... expn) ==> value of expn.






; a produce with the same input but different output
;------------------------------------------------
;example
(define balance 100)

(define (withdrow x)
	(if (>= balance x)
		(begin (set! balance (- balance x))
			   balance)
		"insufficent money!"))


;	(withdrow 40) ==> 60
;	(withdrow 40) ==> 20
;	(withdrow 40) ==> "insufficent money!"

; balance is a global variabale, we can improve it!






; local variable as a state
;------------------------------------------------

(define new-withdrow
	(let ((balance 100)) 
		 (lambda (amount)
		 		 (if (< amount balance)
		 		 	 (begin (set! balance (- balance amount))
		 		 	 		balance)
		 		 	 "insufficent money!"))))
;(new-withdrow 40) ==> 60
;(new-withdrow 40) ==> 60
;(new-withdrow 40) ==> "insufficent money!"


;new-withdrow = function clousure with a environment
;variable 'balance' that is local for global but is a 
;outer variable for 'lambda function'(the function clousure)

;stilly bad style, because it could only be used once!



;improved version
(define make-withdrow
	(lambda (balance)
		(lambda (amount)
		 	(if (< amount balance)
		 		(begin (set! balance (- balance amount))
		 		 	 	balance)
		 		"insufficent money!"))))

;we can make a partial application to 'make-withdrow'
;and get diff function with diff 'balance' in its clousure

(define c1 (make-withdrow 100))
(define c2 (make-withdrow 100))
; c1 c2 is functions the same as new-withdrow

;(c1 40) ==> 60
;(c1 40) ==> 20
;(c2 50) ==> 50
;(c1 30) ==> "insufficent money!"
;(c2 60) ==> "insufficent money!"















