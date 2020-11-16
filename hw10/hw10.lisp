#| 

HW 10: The Proof of the Pudding

|#

#| 

Okay, another single-problem HW assignment. I think this'll be a good
one. Let's do it!

Theorem-heads out there, FYE, please find on the course website my
proof of the <= fib fact claim in Idris, a theorem prover of a very
different sort.

{{ site.baseurl}}/assets/code/factfib.idr

|#

;; In the context of these functions

(definec fact (n :nat) :nat
  (if (= n 0) 1
    (* n (fact (1- n)))))

(definec fib (n :nat) :nat
  (if (< n 2)
    n
    (+ (fib (1- n)) (fib (1- (1- n))))))

(definec fib2 (n :nat) :nat
  (if (zp n)
    0
    (fib-acc2 (1- n) 0 1)))

(definec fib-acc2 (c :nat ans-1 :nat ans :nat) :nat
  (if (zp c)
      ans 
      (fib-acc2 (1- c) ans (+ ans-1 ans))))

;; Our conjecture
(<= (fib2 n) (fact n))

Proof:
(<= (fib2 n) (fact n))
= { Lemma fib-fib2 }
(<= (fib n) (fact n))
= { Lemma conjecture-substituted }
true

Q.E.D.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Lemma conjecture-substituted
(<= (fib n) (fact n))

Induction scheme: natural numbers

Proof obligations:
1. Contract case
(implies (not (natp n)) (<= (fib n) (fact n)))

Contract Completion:
(implies (and (not (natp n)) (natp n))
         (<= (fib n) (fact n)))

Context: 
C1. (not (natp n))
C2. (natp n)
C3. (and (not (natp n)) (natp n)) 

Derived Context:
D1. nil { C1, C2, C3 }

Q.E.D


2. Base case n = 0
(implies (natp n)
  (implies (zp n)
    (<= (fib n) (fact n))))

Exportation:
(implies (and (natp n) (zp n))
  (<= (fib n) (fact n)))
  
Context:
C1. (natp n)
C2. (zp n)

Goal:
(<= (fib n) (fact n))

Proof:
(<= (fib n) (fact n))
= { C1, C2 }
(<= (fib 0) (fact 0))
= { def fib, def fact, if-axioms }
(<= 0 1 )
= { arith }
true

Q.E.D.

3. Base case n = 1
(implies (natp n)
  (implies (= 1 n)
    (<= (fib n) (fact n))))

Exportation:
(implies (and (natp n) (= 1 n))
  (<= (fib n) (fact n)))
  
Context:
C1. (natp n)
C2. (= 1 n)

Goal:
(<= (fib n) (fact n))

Proof:
(<= (fib n) (fact n))
= { C1, C2 }
(<= (fib 1) (fact 1))
= { def fib, def fact, if-axioms }
(<= 1 (* 1 (fact 0)))
= { def fact, if-axioms }
(<= 1 (* 1 1))
= { arith }
(<= 1 1)
= { arith }
true

Q.E.D.
    

4. Induction
(implies (natp n)
  (implies (> n 1)
    (implies (<= (fib (1- n)) (fact (1- n))))
      (<= (fib n) (fact n))))

Exportation:
(implies (and (natp n)
              (> n 1)
              (<= (fib (1- n)) (fact (1- n))))
         (<= (fib n) (fact n)))

Context:
C1. (natp n)
C2. (> n 1)
C3. (<= (fib (1- n)) (fact (1- n)))

Derived Context:
D1. (>= (* n (fact (1- n))) (* 2 (fact (1- n)))) { C2 }
D2. (< (fib (1- n)) (fib (1- (1- n)))) { ... }

Goal:
(<= (fib n) (fact n))

Proof:
(<= (fib n) (fact n))
= { def fib, def fact, C2 }
(<= (+ (fib (1- n)) (fib (1- (1- n)))) (* n (fact (1- n))))
= { C3 }
(<= (+ (fact (1- n)) (fib (1- (1- n)))) (* n (fact (1- n))))
= { arith }
(<= (* (fact (1- n)) (+ 1 (/ (fib (1- (1- n))) (fact (1- n)))) (* n (fact (1- n)))))
= { arith }
(>= n (+ 1 (/ (fib (1- (1- n))) (fact (1- n)))))
= { arith, C2, lemma almost-there }
true

Q.E.D.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Lemma almost-there
(>= 2 (+ 1 (/ (fib (1- (1- n))) (fact (1- n)))))

Context:
C1. (natp n)
C2. (> n 1)
C3. (<= (fib (1- n)) (fact (1- n)))

Derived Context:
D1. (implies 
      (and (<= (fib (1- (1- n))) (fib (1- n))) (<= (fib (1- n)) (fact (1- n))))
      (<= (fib (1- (1- n))) (fact (1- n)))) { arith }

Proof:
(>= 2 (+ 1 (/ (fib (1- (1- n))) (fact (1- n)))))
= { arith }
(>= 1 (/ (fib (1- (1- n))) (fact (1- n))))
= { arith }
(<= (fib (1- (1- n))) (fact (1- n)))
= { lemma getting-closer, C3, D1 }
true

Lemma getting-closer 
(<= (fib (1- n)) (fib n))

Context:
C1. (natp n)
C2. (> n 0)

Induction scheme: natural numbers

No contract case needed because we have (natp n)

Base case (n = 1):
(implies (and (natp n) (> n 0) (< n 2))
         (<= (fib (1- n)) (fib n)))

Context:
C1. (natp n)
C2. (> n 0)
C3. (< n 2)

Derived Context:
D1. (= n 1) { C1, C2, C3 }

Goal:
(<= (fib (1- n)) (fib n))

Proof:
(<= (fib (1- n)) (fib n))
= { D1 }
(<= (fib 0) (fib 1))
= { def fib }
(<= 0 1)
=
true

Q.E.D.


Inductive case:
(implies (and (natp n) (>= n 2))
         (<= (fib (1- n)) (fib n)))
         
Context:
C1. (natp n)
C2. (>= n 2)

Goal:
(<= (fib (1- n)) (fib n))

Proof:
(<= (fib (1- n)) (fib n))
= { Def fib }
(<= (fib (1- n)) (+ (fib (1- n)) (fib (1- (1- n)))))
= { arith }
(<= 0 (fib (1- (1- n))))
= { definition of natural numbers, C1 }
true

Q.E.D.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Lemma fib-fib2

Goal:
(equal (fib2 n) (fib n))

Proof obligations:

Obligation 1:
(implies (and (natp n) (zp n)) 
         (equal (fib2 n) (fib n)))

Context:
C1. (natp n)
C2. (zp n)

Derived Context:
D1. (equal 0 (fib n)) { Def fib, if-axioms, c2 }
D2. (equal 0 (fib2 n)) { Def fib2, if-axioms, c2 }

Goal:
(equal (fib2 n) (fib n))

Proof:
(equal (fib2 n) (fib n))
= { C1, C2, D1, D2 }
true

Q.E.D.

Obligation 2:
(implies (and (natp n) (= 1 n)) 
         (equal (fib2 n) (fib n)))

Context:
C1. (natp n)
C2. (= 1 n)

Derived Context:
D1. (equal (fib n) 1) { def fib, if-axioms }
D2. (equal (fib2 n) (fib-acc2 (1- n) 0 1)) { def fib2, if-axioms }

Proof:
(equal 1 (fib-acc2 (1- n) 0 1))
= { arith, C2 }
(equal 1 (fib-acc2 0 0 1))
= { def fib-acc2, if-axioms }
(equal 1 1)

Q.E.D.


Obligation 3:
(implies (and (natp n) (not (>= n 2)))
         (equal (fib2 n) (fib n)))

Context:
C1. (natp n)
C2. (not (>= n 2))

Derived Context:
D1. (equal (fib n) (+ (fib (1- n)) (fib (1- (1- n))))) { def fib, if-axioms, C1, C2 }
D2. (equal (fib2 n) (fib-acc2 (1- n) 0 1)) { def fib2, if-axioms, C1, C2 }

Goal:
(equal (fib2 n) (fib n))

Proof:
(equal (fib2 n) (fib n))
= { Lemma fib-fib2-induct }
true
Q.E.D.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Lemma fib-fib2-induct

Goal:
(equal (fib2 n) (fib n))

Induction scheme: natural numbers, n >= 2

Proof Obligations:

Obligation 1 (contract case)
(implies (not (natp n)
          (equal (fib2 n) (fib n))))

Obligation 2 (base case n=2)
(implies (natp n)
          (implies (= n 2)
            (equal (fib2 n) (fib n))))

Obligation 3 (base case n=3)
(implies (natp n)
          (implies (= n 3)
            (equal (fib2 n) (fib n))))

Obligation 4 (inductive step)
(implies (natp n)
          (implies (> n 3)
            (implies (and (equal (fib2 (- n 1)) (fib (- n 1))
                          (equal (fib2 (- n 2)) (fib (- n 2)))))
              (equal (fib2 n) (fib n)))))

Proof 1:
(implies (not (natp n))
          (equal (fib2 n) (fib n)))

Context:
C1. (not (natp n))
C2. (natp n) { contract of fib }
C3. (>= n 2)

Derived Context:
D1. nil { C1, C2 }

Q.E.D.

Proof 2:
(implies (and (natp n) (= n 2)) 
    (equal (fib2 n) (fib n)))

Context:
C1. (natp n)
C2. (= n 2)

Proof:
(equal (fib2 n) (fib n))
= { def fib, fib2 }
(equal (+ (fib (1- n)) (fib (1- (1- n)))) (fib-acc2 (1- n) 0 1))
= { C2 }
(equal (+ (fib 1) (fib 0)) (fib-acc2 1 0 1))
= { def fib, if-axioms }
(equal (+ 1 0) (fib-acc2 1 0 1))
= { def fib-acc2, if-axioms }
(equal (+ 1 0) (fib-acc2 0 1 (+ 0 1)))
= { def fib-acc2, if-axioms }
(equal (+ 1 0) 1)
= { arith }
true

Q.E.D.

Proof 3:
(implies (natp n)
          (implies (= n 3)
            (equal (fib2 n) (fib n))))

Exportation:
(implies (and (natp n)
              (= n 3))
         (equal (fib2 n) (fib n)))

Context:
C1. (natp n)
C2. (= n 3)

Proof:
(equal (fib2 n) (fib n))
= { def fib2, fib }
(equal (+ (fib (1- n)) (fib (1- (1- n)))) (fib-acc2 (1- n) 0 1))
= { C2 }
(equal (+ (fib 2) (fib 1)) (fib-acc2 2 0 1))
= { def fib, if-axioms }
(equal (+ (+ (fib 1) (fib 0)) 1) (fib-acc2 2 0 1))
= { def fib, if-axioms }
(equal 2 (fib-acc2 2 0 1))
= { def fib-acc2, if-axioms }
(equal 2 (fib-acc2 1 1 (+ 0 1)))
= { def fib-acc2, if-axioms, arith }
(equal 2 (fib-acc2 0 1 2))
= { def fib-acc2, if-axioms }
(equal 2 2)
=
true 

Q.E.D.

Proof 4:
(implies (natp n)
          (implies (> n 3)
            (implies (and (equal (fib2 (- n 1)) (fib (- n 1))
                          (equal (fib2 (- n 2)) (fib (- n 2)))))
              (equal (fib2 n) (fib n)))))

Exportation:
(implies (and (natp n)
              (> n 3)
              (equal (fib2 (- n 1)) (fib (- n 1))
              (equal (fib2 (- n 2)) (fib (- n 2)))))
         (equal (fib2 n) (fib n)))

Context:
C1. (natp n)
C2. (> n 3)
C3. (equal (fib2 (- n 1)) (fib (- n 1)))
C4. (equal (fib2 (- n 2)) (fib (- n 2)))

Derived Context:
D1. (equal (+ (fib2 (- n 1)) (fib2 (- n 2))
           (+ (fib-acc2 (- n 1) 0 1) (fib-acc2 (- n 2) 0 1))))

Goal:
(equal (fib2 n) (fib n))

Proof:
(equal (fib2 n) (fib n))
= { C2, if-axioms, def fib2 }
;; No way to prove this with regular induction
;; Can't really use inductive hypothesis b/c ans will become 1
(equal (fib-acc2 (1- n) 0 1) (fib n))
= { Lemma fib-acc2-fib, C2 }
(equal (fib-acc2 (1- (1- n)) 1 (+ 1 0)) (fib n))
= { D1 }
(equal (+ (fib (1- n)) (fib (1- (1- n)))) (fib n))
= { def fib }
true

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemma fib-acc2-fib
;; Induction scheme: natural numbers, c < n

;; Proof Obligations

Obligation 1 (contract case)
(implies (not (natp c))
         (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c))) 
                (fib n)))

Obligation 2 (base case c = 0)
(implies (natp c)
         (implies (zp c)
                  (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c))) 
                         (fib n))))

Obligation 3 (inductive step)
(implies (natp c)
         (implies (not (zp c))
                  (implies (equal (fib-acc2 (1- c) (fib (1- (- n (1- c)))) (fib (- n (1- c))))
                                  (fib n))
                           (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
                                  (fib n)))))

;; Proof 1:
(implies (not (natp c))
         (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c))) 
                (fib n)))

;; Contract completion
(implies (and (natp c) (not (natp c)))
         (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
                (fib n)))
;; Goal
(equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c))) 
                (fib n))

;; Context
C1. (not (natp n))
C2. (natp n)

;; Derived Context
D1. nil { C1, C2 }

Q.E.D

;; Proof 2:
;; Conjecture
(implies (natp c)
         (implies (zp c)
                  (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c))) 
                         (fib n))))

;; Exportation
(implies (and (natp c)
              (zp c))
         (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c))) 
                (fib n)))

;; Context
C1. (natp c)
C2. (zp c)

;; Goal
(equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
                (fib n))
;; Proof
(fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
= { C2 }
(fib (- n c))
= { Arith, C2 }
(fib n)
true
Q.E.D.

;; Proof 3
;; Conjecture
(implies (natp c)
         (implies (zp c)
                  (implies (equal (fib-acc2 (1- c) (fib (1- (- n (1- c)))) (fib (- n (1- c))))
                                  (fib n))
                           (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
                                  (fib n)))))
;; Exportation
(implies (and (natp c)
              (not (zp c))
              (equal (fib-acc2 (1- c) (fib (1- (- n (1- c)))) (fib (- n (1- c))))
                     (fib n)))
         (equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
                (fib n)))

;; Goal
(equal (fib-acc2 c (fib (1- (- n c))) (fib (- n c)))
       (fib n))

;; Context
C1. (natp c)
C2. (not (zp c))
C3. (equal (fib-acc2 (1- c) 
                     (fib (1- (- n (1- c))))
                     (fib (- n (1- c))))
           (fib n))

;; Derived Context
D1. (= (- n c) (1- (- n (1- c)))) { Arith }
D2. (= (+ (fib (1- (- n c))) (fib (- n c)))
       (fib (- n (1- c)))) { Def fib }

;; Proof
(fib-acc2 c 
          (fib (1- (- n c))) 
          (fib (- n c)))
= { Def fib-acc 2, if-axioms, C2 }
(fib-acc2 (1- c) 
          (fib (- n c))
          (+ (fib (1- (- n c))) (fib (- n c))))
= { D1, D2 }
(fib-acc2 (1- c) 
          (fib (1- (- n (1- c)))) 
          (fib (- n (1- c))))
= { C3 }
(fib n)
true
Q.E.D.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Part II: A not-part of your homework.

You all. This is not a part of your homework. You are not required to
turn anything in for this. However, if you treat it like your
homework, you'll be better prepared. I would like each posse to meet
with me via Zoom, for approximately ~10m, after having sent a
suggestion of the statement that they wish to prove in ACL2. Using
ACL2, to do actual theorem-proving work, not just pen-and-paper for
it.

Alternately, if your group has some other kind of idea for something
related to theorem proving---if for instance your mob has experience
with Agda and you want to pursue something related to that, that's a
suggestion. If you find yourselves really intrigued by Prolog or
miniKanren and want to try your hand with something related that way,
I can help guide you. If you are by chance interested in non-classical
logics or alternate proof systems and think you've got something
interesting to say or to do here (if any, I would suggest trying to
make an educational, pedagogical contribution) that too might strike
your fancy.

But please be prepared to schedule a meeting with me on or hopefully
between this Saturday the 14th and Wednesday the 18th of next week.
When you schedule that meeting, send me a couple of paragraphs
describing what you want to do. No need for grammatical flourishes; I
want to put you all on a good, right track ASAP. Maybe have a back-up
idea in your back pocket?

FWIW, I'm expecting something maybe less ambitious in scope that we
did mid-semester, but also consider mechanical proofs will likely not
require nearly so much documentation. Think about something slightly
more than these 1-week homework questions, but certainly less than the
Church-Rosser theorem.

I'll ask to receive a progress report from you all on the 30th, when
we return from break, with an ultimate due date Wed, Dec
9th. Presentations will have to be due on or before the 9th also.

At student's/mob's requests, I can be persuaded to, for just this once
to accept some late assignments---say, give you the weekend to put on
finishing touches, and to have met with me on or before the evening of
the 14th. However, I certainly can't and wouldn't mandate that.

|# 
