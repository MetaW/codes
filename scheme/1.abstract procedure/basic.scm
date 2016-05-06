;在终端输入(cf "filename")进行编译
;之后再输入(load "filename")进行加载

;在终端中进入error后输入(RESTART 1)恢复到正常
;每次打开后要先分屏再开一个终端窗口以方面调试，方法Tools->SublimeREPL->scheme
;＊注意打开SublimeREPL时要先把光标放到代码编辑区，这样终端的工作目录才会定位到代码所在的目录下
;每次打开都要为终端窗口设置syntex为scheme,以显示颜色和提示,方法View->syntex->scheme


;scheme中的递归函数并非都做递归计算，其计算过程分为：
;递归计算过程和迭代计算过程
;迭代计算过程是不保留状态的尾递归由编译器优化得来的

;constant binding
(define aa 100)

;function binding
(define (myadd x y)
	(+ x y))

;if
(define (fact x)
	(if (= x 1)
		1
		(* x (fact (- x 1)))))

;call a function
(myadd 12 12)


; cond 
; 线性递归
(define (Ack x y)
	(cond 	((= y 0) 0)
	      	((= x 0) (* 2 y))
	      	((= y 1) 2)
	      	(else (Ack (- x 1) (Ack x (- y 1))))))

;(Ack 1 10)


;bool
(define bb (= 1 2))			;bb = #f
(define cc (and bb #t))		;cc = #f
(define dd (or bb #t))		;dd = #t
(define ee (not bb))		;ee = #t



;local binding
;可以嵌套多层
(define (ff x)
	(define (f x)
		(define (tf x)
			(* x x))
		(tf x)) 
	(define (g x)
	  	(+ x x))
	(f (g x)))



;树形递归
(define (fib n)
  	(cond 	((= n 0) 0) 
  			((= n 1) 1) 
  			(else (+ 
  					(fib (- n 1))
  					(fib (- n 2))))))


;树形递归改迭代
(define (fib_iter a b n)
  	(if (= n 0) a 
  		(fib_iter b (+ a b) (- n 1))))

(define (fib2 n)
  	(fib_iter 0 1 n))

;exercise 1.11
(define (f n)
	(cond ((< n 3) n)
	      (else (+	(f (- n 1))
	      			(* 	2 
	      				(f (- n 2)))
	      			(* 	3 
	      				(f (- n 3)))))))


;gcd
(define (gcd n m)
  	(if (= n 0) 
  		m
  		(gcd (remainder m n) n)))




;;高阶函数
;------------------------------------------------
; g(f,a b) = sum(f n){n = a,a+1,..,b}
(define (sum f a next b)
	(if (> a b) 
		0
		(+ 	(f a) 
			(sum f (next a) next b))))

;具像化
(define (inc x) (+ x 1))

;求立方和
(define (cube x) (* x x x))
(define (sum_cube a b)
	(sum cube a inc b))


;迭代计算过程的sum
(define (sum2 f a next b)
	(define (iter cur a)
		(if (> a b) 
			cur
			(iter (+ cur (f a)) (next a))))
	(iter 0 a))

;求积分
(define (integral f a b dx)
	(define (add_dx x) (+ x dx))
	(* 	(sum2 f (+ a (/ dx 2.0)) add_dx b)
		dx))
;example
(integral cube 1 10 0.001)


;匿名函数
;------------------------------------------------
;lambda函数可以出现在所有能调用函数的地方
;eg: ((lambda (x) (+ x 1)) 5) 值为6
;如何处理匿名函数的递归问题？？？？？

;重新定义intergral
(define (integral2 f a b dx)
	(* 	(sum2 f (+ a (/ dx 2.0)) (lambda (x) (+ x dx)) b)
		dx))



;;;;let定义局部变量(使用匿名函数的语法糖)
;一般我们习惯用define定义局部函数,let定义局部变量,当然这不是必须的
(define (ff1 x y)
	(define a (+ x y))	;定义局部变量
	(define b (- x y))
	(* 	(+ a b)
		(- a b)))


;还可以用lambda函数实现
(define (ff2 x y)
	((lambda (a b)
		(* 	(+ a b)
			(- a b)))
	(+ x y)
	(- x y)))

;转化为let
(define (ff3 x y)
	(let   ((a (+ x y))
			(b (- x y))) 
		(* 	(+ a b)
			(- a b))))

;let的语法：
;
;(let 	((var exp)
;		 (var exp)
;		 (var exp))
;	(body))
























