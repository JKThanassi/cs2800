#|

HW 7. More Admission and Definition

|#

#|

Once again, you are welcome to try these functions on ACL2s, but you cannot just
report what ACL2s reports to you. You have to provide your own arguments for
or against admissibility, as per instructions above.

For each definition below, check whether it is admissible, i.e., it
satisfies all conditions of the Definitional Principle. You can assume
that Condition 1 is met: the symbol used is a new function symbol.

A. If you claim that the function is admissible:

a) provide a measure function that can be used to prove termination

b) state the contract theorem (condition 5)

c) prove that the function is terminating using your measure function
   and equational reasoning

B. If you claim the function is not admissible, identify a condition 
   that is violated, subject to:

  - If conditions 2 or 3 are violated (formals are not distinct or
    body is not a term), explain the violation in English. 

  - If one of the other conditions is violated, provide an input that
    satisfies the input contract but causes the condition to
    fail. 
 
  - Even if multiple conditions are violated, you only have to find
    one such condition. 

|#

;; 1
 
(definec f1 (x :nat y :nat z :nat) :nat
  (cond
    ((and (equal x 0) (equal y 0) (equal z 0)) 0)
    ((and (<= x y) (<= x z)) (f1 (- x 1) (- y 1) (- z 1)))
    ((and (<= y x) (<= y z)) (f1 (- x 1) (- y 1) (- z 1)))
    ((and (<= z x) (<= z y)) (f1 (- x 1) (- y 1) (- z 1)))
    (t 0)))

#|

A. The function is not admissible. Counterexample: 
((X 0) (Y 5) (Z 812))

|#

;; 2
 
(definec f2 (x :tl y :tl acc :tl) :tl
  (if (endp x)
      (if (endp y)
          acc
        (f2 x (rest y) (cons (first y) acc)))
    (f2 (rest x) y (cons (first x) acc))))


;; A. The function is admissible.

;; Contract thm IC => OC

(thm (implies (and (tlp x) (tlp y) (tlp acc))
              (tlp (f2 x y acc))))

;; Contract thm IC-f2 => IC-m-f2
(thm (implies (and (tlp x) (tlp y) (tlp acc))
              (and (tlp x) (tlp y))))

;; The measure function is as follows:

(definec m-f2 (x :tl y :tl acc :tl) :nat
  (declare (ignorable acc))
         (+ (len x) (len y)))

;; proof as follows
;; Conjecture 1:
(thm (implies (and (tlp x) (tlp y) (tlp acc) (not (endp x)) (not (endp y)))
         (> (m-f2 x y acc) (m-f2 (rest x) y acc))))
;; Context:
;; C1. (tlp x)
;; C2. (tlp y)
;; C3. (tlp acc)
;; C4. (not (endp x))
;; C5. (not (endp y))
;;
;; Goal:
;; (> (m-f2 x y acc) (m-f2 (rest x) y acc))

;; Proof:
;; (> (m-f2 x y acc) (m-f2 (rest x) y acc))
;; = { def m-f2 }
;; (> (+ (len x) (len y)) (+ (len (rest x)) (len y)))
;; = { lemma cons-size, if-axioms }
;; (> (+ (+ 1 (len (rest x))) (len y)) (+ (len (rest x)) (len y)))
;; = { arith }
;; True
;; QED
;;
;; 3

(definec f3 (x :tl y :tl acc :tl) :tl
  (cond
    ((and (endp x) (endp y)) acc)
    ((endp x) (f3 x (rest y) (cons (first y) acc)))
    ((endp y) (f3 (rest x) y (cons (first x) acc)))
    (t (f3 x nil (f3 nil y acc)))))

#| 

A. Admissible

;; a) Generalized Measure Function
(definec mf3 (x :tl y :tl) :nat
  (+ (len x) (len y)))
  
;; f3 IC => mf3 IC
(implies (and (tlp x) (tlp y) (tlp acc))
         (and (tlp x) (tlp y)))

;; b) Contract Theorem
(implies (and (tlp x) (tlp y) (tlp acc))
         (tlp (f3 x y acc)))

;; c) Termination Proofs
Conjecture 1:
(implies (and (tlp x) (tlp y) (tlp acc) (endp x) (consp y))
         (< (mf3 x (rest y)) (mf3 x y)))
Context:
C1. (tlp x)
C2. (tlp y)
C3. (tlp acc)
C4. (endp x)
C5. (consp y) 

Goal: (< (mf3 x (rest y)) (mf3 x y))

Proof:
(< (mf3 x (rest y)) (mf3 x y))
= { Def mf3, C1, C2, C4, C5 }
(< (+ (len x) (len (rest y))) (+ (len x) (len y)))
= { Def len, C4, C5 }
(< (+ 0 (len (rest y))) (+ 0 (len y)))
= { arith, cons-size axiom }
(< (1- (len y)) (len y))
= { arith }
(< -1 0)
QED

Conjecture 2:
(implies (and (tlp x) (tlp y) (tlp acc) (consp x) (endp y))
         (< (mf3 (rest x) y) (mf3 x y)))
Context:
C1. (tlp x)
C2. (tlp y)
C3. (tlp acc)
C4. (endp x)
C5. (consp y) 

Goal: (< (mf3 (rest x) y) (mf3 x y))

Proof:
(< (mf3 (rest x) y) (mf3 x y))
= { Def mf3, C1, C2, C4, C5 }
(< (+ (len (rest x)) (len y)) (+ (len x) (len y)))
= { Def len, C4, C5 }
(< (+ (len (rest x)) 0) (+ (len x) 0))
= { arith, cons-size axiom }
(< (1- (len x)) (len x))
= { arith }
(< -1 0)
QED

Conjecture 3:
(implies (and (tlp x) (tlp y) (tlp acc) (consp x) (consp y))
         (< (mf3 x nil) (mf3 x y)))
Context:
C1. (tlp x)
C2. (tlp y)
C3. (tlp acc)
C4. (consp x)
C5. (consp y)

Goal: (< (mf3 x nil) (mf3 x y))

Proof:
(< (mf3 x nil) (mf3 x y))
= { Def mf3, C1, C2, C4, C5 }
(< (+ (len x) (len nil)) (+ (len x) (len y)))
= { Def len, C4, C5 }
(< (+ (len x) 0) (+ (len x) (len y)))
= { arith }
(< (len x) (+ (len x) (len y)))
= { C5, arith }
(< 0 (len y))
QED

B.

|#

;; 4

;(definec f4 (x :tl y :tl acc :tl) :tl
;  (cond
;    ((and (endp x) (endp y)) acc)
;    ((endp x) (f4 x (rest y) (cons (first y) acc)))
;    ((endp y) (f4 y x acc))
;    (t (f4 x nil (f4 acc nil y)))))

#| 

A. Admissible (commented out because ACL2S would not accept it)

;; a) Generalized Measure Function
(definec mf4 (x :tl y :tl acc :all) :nat
  (cond 
   ((endp x) (len y))
   ((endp y) (1+ (len x)))
   (t (+ 2 (len acc) (len x)))))
   
;; f4 IC => mf4 IC
(implies (and (tlp x) (tlp y) (tlp acc))
         (and (tlp x) (tlp y) (allp acc)))

;; b) Contract Theorem
(implies (and (tlp x) (tlp y) (tlp acc))
         (tlp (f4 x y acc)))

;; c) Termination Proofs
Conjecture 1:
(implies (and (tlp x) (tlp y) (tlp acc) (endp x) (consp y))
         (< (mf4 x (rest y) (cons (first y) acc)) (mf4 x y acc)))
Context:
C1. (tlp x)
C2. (tlp y)
C3. (tlp acc)
C4. (endp x)
C5. (consp y)

Goal: (< (mf4 x (rest y) (cons (first y) acc)) (mf4 x y acc))

Proof:
(< (mf4 x (rest y) (cons (first y) acc)) (mf4 x y acc))
= { Def mf4, C1, C2, C3, C4, C5 }
(< (len (rest y)) (len y))
= { cons-size axiom, C5 }
(< (1- (len y)) (len y))
= { arith }
(< -1 0)
QED

Conjecture 2:
(implies (and (tlp x) (tlp y) (tlp acc) (consp x) (endp y))
         (< (mf4 y x acc) (mf4 x y acc)))
Context:
C1. (tlp x)
C2. (tlp y)
C3. (tlp acc)
C4. (consp x)
C5. (endp y)

Goal: (< (mf4 y x acc) (mf4 x y acc))

Proof:
(< (mf4 y x acc) (mf4 x y acc))
= { Def mf4, C1, C2, C3, C4, C5 }
(< (1+ (len y)) (1+ (len x)))
= { Def len, C5 }
(< (1+ 0) (1+ (len x)))
= { arith, C4 }
(< 0 (len x))
QED

Conjecture 3:
(implies (and (tlp x) (tlp y) (tlp acc) (consp x) (consp y))
         (< (mf4 x nil (mf4 acc nil y)) (mf4 x y acc)))
Context:
C1. (tlp x)
C2. (tlp y)
C3. (tlp acc)
C4. (consp x)
C5. (consp y)

Derived Context:
D1. (allp (mf4 acc nil y)) { mf4 output contract }

Goal: (< (mf4 x nil (mf4 acc nil y)) (mf4 x y acc))

Proof:
(< (mf4 x nil (mf4 acc nil y)) (mf4 x y acc))
= { Def mf4, C1, C2, C3, C4, C5, D1 }
(< (1+ (len x)) (+ 2 (len acc) (len x)))
= { arith, C3 }
(< 0 (1+ (len acc)))
QED

B.

|#

;; 5
;; Commented out because ACL2S won't accept it
(definec f5 (x :nat l :tl a :all) :all
  (cond
    ((endp l) a)
    ((== x 0) 1)
    ((oddp x) (f5 (1- x) l a))
    ((> x (len l)) (f5 (/ x 2) l x))
    (t (f5 x (rest l) (first l)))))


;; Measure Function
|#

(definec m5 (x :nat l :tl a :all) :nat
  (declare (ignorable a))
  (cond ((endp l) 0)
        ((== x 0) 0)
        (t (+ x (len l)))))

;; Admissable

;; Contract Theorem

(thm (implies (and (natp x) (tlp l) (allp a))
              (natp (f5 x l a))))

;; Conjectures
(thm (implies (and (natp x)
                   (tlp l)
                   (allp a)
                   (not (endp l))
                   (not (== x 0))
                   (not (oddp x))
                   (> x (len l)))
              (< (m5 (/ x 2) l x) (m5 x l a))))

(thm (implies (and (natp x)
                   (tlp l)
                   (allp a)
                   (not (endp l))
                   (not (== x 0))
                   (not (oddp x))
                   (not (> x (len l))))
              (< (m5 x (rest l) (first l)) (m5 x l a))))

;; Proof
; Conjecture 1
(implies (and (natp x)
              (tlp l)
              (allp a)
              (not (endp l))
              (not (== x 0))
              (not (oddp x))
              (> x (len l)))
         (< (m5 (/ x 2) l x) (m5 x l a)))

; Context
C1. (natp x)
C2. (tlp l) 
C3. (allp a)
C4. (not (endp l))
C5. (not (== x 0))
C6. (not (oddp x))
C7. (> x (len l))

; Derived Context
D1. (implies (and (natp x) (not (== x 0))) (< (/ x 2) x)) { Def /, C1, C5, C6 }

; Goal: (< (m5 (/ x 2) l x) (m5 x l a))

; Proof
(< (m5 (/ x 2) l x) (m5 x l a))
= { Def m5 }
(< (cond ((endp l) 0)
         ((== (/ x 2) 0) 0)
         (t (+ (/ x 2) (len l))))
   (cond ((endp l) 0)
         ((== x 0) 0)
         (t (+ x (len l))))
= { C4, C5 }
(< (+ (/ x 2) (len l))
   (+ x (len l)))
= { Arithm }
(< (/ x 2) x)
= { D1 }
t

; Conjecture 2
(implies (and (natp x)
              (tlp l)
              (allp a)
              (not (endp l))
              (not (== x 0))
              (not (oddp x))
              (not (> x (len l))))
         (< (m5 x (rest l) (first l)) (m5 x l a)))

; Context
C1. (natp x)
C2. (tlp l) 
C3. (allp a)
C4. (not (endp l))
C5. (not (== x 0))
C6. (not (oddp x))
C7. (not (> x (len l)))

; Derived Context
D1. (implies (and (not (oddp x)) (not (== x 0)) (not (> x (len l))))
             (and (> x 1) (> (len l) 2) (not (endp (rest l))))) { Arith, C4, C5, C6, C7 }

; Goal: (< (m5 x (rest l) (first l)) (m5 x l a))

; Proof
(< (m5 x (rest l) (first l)) (m5 x l a))
= { Def m5 }
(< (cond ((endp (rest l)) 0)
         ((== x 0) 0)
         (t (+ x (len (rest l)))))
   (cond ((endp l) 0)
         ((== x 0) 0)
         (t (+ x (len l))))
= { C4, C5, D1 }
(< (+ x (len (rest l)))
   (+ x (len l)))
= { Arith }
(< (len (rest l)) (len l))
= { Def rest, Def len, C4 }
t

QED
|#


#| BONUS PROBLEM 

This is not a requirement, or for points. Instead, this is for dessert
and bragging rights.

But doable! If you attempt, I suggest 

a) reading to the end of this chapter and, 
b) testing only with small numbers!! 

(definec harvey (m :nat n :nat) :nat
  (cond
    ((zp n) 1)
    ((zp (1- m)) (* 2 n))
    (t (harvey (1- m) (harvey m (1- n)))))))

(definec h (n :nat) :nat
  (harvey n n))

|#

