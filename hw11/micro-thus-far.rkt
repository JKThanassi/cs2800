#lang racket

(define (var? n) (number? n))
(define (var n) n)

;; GroundTree oneof 
;; cons GroundTree GroundTree
;; symbol
;; null

;; Tree oneof
;; cons Tree Tree
;; symbol
;; null
;; vars

(cons 'cat (cons 'dog 0))

(cons 'fish (cons 0 1))

;; Substs
;; Alsist of Var x Tree

;; ()
;; ((0 . cat))
;; ((1 . fish) (0 . cat))
;; ((1 . starfish) (0 . 1))

;; Var x Susbt -> Tree
(define (walk x s)
  (let ((pr (assv x s)))
    (if pr (walk (cdr pr) s) x)))

;; Var x Tree x Subst -> Bool
(define (occurs? x t s)
  (cond
    ((var? t) (eqv? x t))
    ((cons? t) (or (occurs? x (walk (car t) s) s)
                   (occurs? x (walk (cdr t) s) s)))
    (else #f)))

;; Var x Tree x Subst -> Maybe Subst
(define (ext-s x t s)
  (cond
    ((occurs? x t s) #f)
    (else (cons (cons x t) s))))

;; Tree X Tree X Subst -> Maybe Subst
(define (unify u v s)
  (let ((u (walk u s))
        (v (walk v s)))
    (cond
      ((eqv? u v) s) ;; if they're already the same var
      ((var? u) (ext-s u v s)) ;; u is a var and they aren't already the same
      ((var? v) (ext-s v u s))
      ((and (cons? u) (cons? v))
       (let ((s^ (unify (car u) (car v) s)))
         (and s^ (unify (cdr u) (cdr v) s^))))
      (else #f))))


;; Subst x Counter
;; (() . 15)

;; Goal :: State -> List 

;; Term X Term -> Goal 
(define (== u v)
  (lambda (s)
    (let ((s^ (unify u v (car s))))
      (if s^ (list (cons s^ (cdr s))) '()))))

(define (run/s g)
  (g '(() . 0)))

;; (lambda Var Goal) 

;; Var->Goal -> Goal 
(define (call/fresh f)
  (lambda (s)
    (let ((c (cdr s)))
      ((f c) (cons (car s) (+ 1 c))))))

;; call this f (lambda (x) (== x 'cat))
;; call this s '(() . 0)
;; call c 0
;; (f c) is a goal
;; ((== x 'cat) (() . 1)) (where we know x is 0)

;; List x List -> List
(define ($app l1 l2)
  (cond
    ((empty? l1) l2)
    (else (cons (car l1) ($app (cdr l1) l2)))))

;; Goal X Goal -> List
(define (disj g1 g2)
  (lambda (s)
    ($app (g1 s) (g2 s))))

(define ($appm l g)
  (cond
    ((empty? l) '())
    (else ($app (g (car l)) ($appm (cdr l) g)))))

;; Goal X Goal -> List
(define (conj g1 g2)
  (lambda (s)
    ($appm (g1 s) g2)))

