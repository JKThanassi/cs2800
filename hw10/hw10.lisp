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
  (if 0 1
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

;; Go to it!


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
(equal (fib2 n) (fib n)))
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

Context:
C1. (natp n)
C2. (= n 3)

Proof:
(equal (fib2 n) (fib n)))
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

Context:
C1. (natp n)
C2. (> n 3)
C3. (equal (fib2 (- n 1)) (fib (- n 1)))
C4. (equal (fib2 (- n 2)) (fib (- n 2)))

Proof:
Goal: 
(equal (fib2 n) (fib n))

(equal (fib2 n) (fib n))
= { C2, if-axioms, def fib }
(equal (fib2 n) (+ (fib (- n 1)) (fib (- n 2))))
= { C3, C4 }
(equal (fib2 n) (+ (fib2 (- n 1)) (fib2 (- n 2))))
= { def fib, C2, if-axioms }
(equal (fib-acc2 (1- n) 0 1)
       (+ (fib-acc2 (1- (- n 1)) 0 1)
          (fib-acc2 (1- (- n 2)) 0 1)))
= { arith }
????????????????????????


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
