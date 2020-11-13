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


;; Let me gently hint that, you will very likely want to show first

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
D1. (equal (fib n) (+ (fib (1- n)) (fib (1- (1- n))))) { def fib }
D2. (equal (fib2 n) (fib-acc2 (1- n) 0 1)) { def fib2 }

Goal:
(equal (fib2 n) (fib n))

Proof:
(equal (fib2 n) (fib n))
= { Lemma 1 }
true
Q.E.D.


Lemma 1:
()



Context:

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
