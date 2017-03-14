#lang plai-typed

(define-type (Maybe 'a)
  (Just (v : 'a))
  (Error))


; bad stype
(define devide : ((Maybe number) (Maybe number) -> (Maybe number))
  (lambda (x y)
    (type-case (Maybe number) x
      (Just (vx)
            (type-case (Maybe number) y
              (Just (vy) (if (= vy 0) (Error) (Just (/ vx vy))))
              (Error () (Error))))
      (Error () (Error)))))



;try another way
(define tedious-stuff : ((Maybe number) (number -> (Maybe number)) -> (Maybe number))
  (lambda (k f)
    (type-case (Maybe number) k
      (Just (vk) (f vk))
      (Error () (Error)))))


(define devide2 : ((Maybe number) (Maybe number) -> (Maybe number))
  (lambda (x y)
    (tedious-stuff x
                   (lambda (vx)
                     (tedious-stuff y
                                    (lambda (vy)
                                      (if (= 0 vy)
                                          (Error)
                                          (Just (/ vx vy)))))))))

;define a syntex
(define-syntax do
  (syntax-rules (<-)
                [(do (vx <- x) (vy <- y) e)
                 (tedious-stuff x
                    (lambda (vx)
                      (tedious-stuff y
                         (lambda (vy)
                           e))))]))
;final version
(define devide3 : ((Maybe number) (Maybe number) -> (Maybe number))
  (lambda (x y)
    (do (a <- x)
        (b <- y)
        (if (= b 0) (Error) (Just (/ a b))))))


;other function
(define my-add ; ((Maybe number) (Maybe number) -> (Maybe number))
  (lambda (x y)
    (do (a <- x)
        (b <- y)
        (Just (+ a b)))))


;Do we need to redefine all functions? of course not!
;we can 'lift' functions to work as intended
(define lift ; (('a 'b -> 'c) (Maybe 'a) (Maybe 'b) -> (Maybe 'c))
  (lambda (f)
    (lambda (x y)
      (do (a <- x)
          (b <- y)
          (Just (f a b))))))

(define my-add2 (lift +))

;;;
;A monad is completely defined by:
;• A type constructor to have values of type M A
;• A ’unit’ or ’return’ function with type A -> M A
;• A ’bind’ function with type: M A -> (A -> MB) -> M B


;Maybe Monad

;Type constructor :
;(define-type Maybe (Just (v any?)) (Error))

;Unit:
; A -> Maybe A
;(define (unit v) (Just v))

;Binder:
; M A -> (A -> M B) -> M B
;(define (bind k f)
;    (type-case Maybe k
;      (Just (v) (f v))
;      (Error () (Error))))
