#lang racket

;eval apply loop
(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
  		((variable? exp) (lookup-var-value exp evn))
  		((quoted? exp) (text-of-quotation exp))
  		((assignment? exp) (eval-assignment exp env))
  		((definition? exp) (eval-definition exp env))
  		((if? exp) (eval-if exp evn)) 
  		((lambda? exp)
  			(make-proc (lambda-params exp)
  					   (lambda-body exp)
  					   env))
  		((begin? exp) 
  			(eval-sequence (begin-actions exp) env))
  		((cond? exp) (eval (cond->if exp) env))
  		((application? exp)
  			(apply (eval (operator exp) env)
  				   (list-of-values (operands exp) env)))
  		(else (error "Unknow expression type -- EVAL" exp))))

  
(define (apply proc args)
  (cond ((primitive-proc? proc)
  			(apply-primitive-proc proc args))
  		((compound-proc? proc)
  			(eval-sequence (proc-body proc)
  						   (extend-env  (proc-params proc)
  						   				args
  						   				(proc-env proc))))
  		(else (error "Unknow procedual type -- APPLY" proc))))


(define (list-of-values exps env)
  ())

(define (eval-if exp env)
  ())

(define (eval-sequence exps env)
  ())

(define (eval-assignment exp evn)
  ())

(define (eval-definition exp env)
  ())



