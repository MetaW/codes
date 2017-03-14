;===============================================================
; define a module :
;---------------------- two ways:
#lang racket

; by default, everything inside a module is private.
(provide (all-defined-out)) ; this line make everything public.

(define a 123)
(define b "asc")


;----------------------  equals to :
(module mymodule racket

  (provide (all-defined-out))

  (define aa 123)
  (define bb "dwc")
  
  )


;;;;; use a module:
(require "filename.rkt")







;===============================================================
;local binding : let, let*, letrec, define

;-----
;1. let : exp are evaled in the env out side it for every binding.

(define x 10)
(define t1
  (let ([x 1]         ; x = 10
        [y (+ x 1)])  ; x = 1
    (...)))

;-----
;2. let* : exp are evaled in the env produced from the privious binding.
(define t2
  (let* ([x 1]
         [y (+ x 1)])
    (...)))

;equals to :
(define t2
  (let ([x 1])
    (let ([y (+ x 1)])
      (...))))

;-----
;3. letrec : exp are evaled in the env that included all the bindings of this letrec. Use define mutual recsive function.
;!!!! ATTENTION: letrec binding allow access binding defined in everywhere of the same scope, that is the sequence is not
;matter, HOWEVER, letrec does not allow shadowing, you can not define a variable twice in the same scope.

(define t3
  (letrec ([f (lambda () (+ a b))]
           [a 1]
           [b 2])
    (...)))

(define t4
  (letrec ([even? (lambda (n) (if (= n 0) #t (odd? (- n 1))))]
           [odd? (lambda (n) (if (= n 0) #f (even? (- n 1))))])
    (...)))

;-----
;4. define : for define local vars it is the same as letrec.

(define t5
  (define (even? (lambda (n) (if (= n 0) #t (odd? (- n 1))))))
  (define (odd? (lambda (n) (if (= n 0) #f (even? (- n 1))))))
  (...))







;===============================================================
;-----top level bindings






;===============================================================
;-----macro system
; macro system works at the level of tokens not string.

(define-syntax my-if
  (syntax-rules (then else)
                [(my-if e1 then e2 else e3)  ; self defined concerte syntex tree
                 (if e1 e2 e3)]              ; original concrete syntex tree
                [...]
                [...]))

