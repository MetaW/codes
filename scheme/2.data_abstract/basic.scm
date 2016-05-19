

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





;programming in sequence transforming
;----------------------------------------------------------

; 1.generate a sequence
;---pass

; 2(a).使用map进行转换
(define (squire_list li)
	(map (lambda (x) (* x x)) li))


; 2(b).使用filter进行过滤
(filter odd? (list 1 2 3 4 5 6))


; 3.accumulate
(fold + 0 (list 1 2 3 4))



;例子:求二叉树的值为奇数的叶子结点的平方和
;1.generate a seq: transform a tree to a seq

(define tr (list 1 (list 2 3) (list 4 5)))

(define (eunm_tree tree)
	(cond 	((null? tree) ())
	      	((not (pair? tree)) (cons tree ()))
	      	(else (append 
	      				(eunm_tree (car tree)) 
	      				(eunm_tree (cdr tree))))))


;2.使用filter过滤留下odd数

(define ftr (filter odd? (eunm_tree tr)))

;3.使用map进行square

(define mftr (map square ftr))

;4.accumulate

(define ans (fold + 0 mftr))


;将2.3.4合在一起
(define ans2 (fold 	+ 
					0 
					(map square
						 (filter odd?
						 		 (eunm_tree tr)))))



;;;exercise2.33
(define (myfold f e seq)
	(cond ((null? seq) e)
	      (else (f  (car seq)
	      			(myfold f e (cdr seq))))))

(define (mymap f seq)
	(myfold (lambda (x y) 
				(cons (f x) y)) 
		  () 
		  seq))

(define (myappend ls1 ls2)
	(myfold cons 
		  ls2
		  ls1))


(define (mylength seq)
	(myfold (lambda (x y)
					(+ 1 y))
			0
			seq))

;;;exercise2.37
;sometimes you need to define your own map to solve a 
;more complex problem. eg:
(define (comap f x w)
	(cond ((null? x) ())
	      (else (cons (myfold + 0 
	      					  (map (lambda (t) (* t (car x))) 
	      					  	   (car w))) 
		       		  (comap f (cdr x) (cdr w))))))		

(define (dotmap f v w)
	(map (lambda (row) (comap * row w)) v))

(define (dot_prod v w)
	(myfold + 0 (map (lambda (x) (fold + 0 x)) 
					 (dotmap * v w))))


;2
(define (map2x f x y)
	(cond ((null? y) 
				(map (lambda (a) (cons a ())) x))
		  ((null? x) ())
	      (else (cons (f (car x) (car y))
	      			  (map2x f (cdr x) (cdr y))))))

(define (foldn r li)
	(map2x cons r li))

(define (trans m)
	(myfold foldn () m))


;;;exercise2.38
;执行顺序
;(fold_right f E (list a b c d))
;= (f a (f b ( f c ( f d E)))

;(fold_left f E (list a b c d))
;= (f(f(f(f E a) b) c) d)


;;;exercise2.39
;用fold-left与fold-right分别实现reverse函数

(define (myreverse1 seq)
	(fold-left (lambda (x y) (cons y x)) () seq))

(define (myreverse2 seq)
	(fold-right (lambda (x y) (append y (list x))) () seq))



;枚举一个list的所有排列
;当map将每一个元素都转换成一个list时
;就要注意是否需要使用flatmap
(define (flatmap f seq)
	(myfold append () (map f seq)))


(define (remove ls x)
	(filter (lambda (t) (not (= t x))) ls))

(define (permutation ls)
	(cond ((null? ls) (list (list)))
	      (else (flatmap (lambda (x) 
	      				 	(map (lambda (t) (cons x t)) 
	      					  	 (permutation (remove ls x)))) 
	      			     ls))))







