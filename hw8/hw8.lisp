#| 

HW 8: Undecidability Results and Induction

|#

#| 

Part I: DIAGONALIZATION

Using a diagonalization argument as described in section 5.4.2 and
used in 5.4.2 and 5.4.4, demonstrate the nondenumerability of the real
numbers 0<=r<=1. Hint: you might find this especially elegant if you
work in base 2. Like the examples from the book, this should look much
closer to an "informal proof" from a math class than to an ACL2 or
pen-and-paper proof.

|#

#| 

Part II: FINISHING THAT PROOF BY INDUCTION 

You will complete the following proof, including the required
lemmata. I will indicate when we "get stuck" and need to resort to a
lemma. We will go complete that lemma, and return when we're finished.

With the pieces you've gathered from lab, and also from what you've
learned as a result of doing it, you should be ready and able to
complete the big proof!

|#

;; Ye olde pre-existing defnns
 (definec app2 (x :tl y :tl) :tl
	(if (endp x)
		y
	  (cons (first x) (app2 (rest x) y))))

  (definec rev2 (x :tl) :tl
	(if (endp x)
		x
	  (app2 (rev2 (cdr x)) (list (car x)))))

#| 

Lemma 2b: rev-app-base
;; Conjecture
(implies (tlp x)
  (implies (endp x)
	  (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x)))))

;; Exportation
(implies
 (and (tlp x)
      (endp x))
 (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))

;; Contract completion:
(implies
 (and (tlp x)
      (tlp y)
      (endp x)
      (tlp (app2 x y))
      (tlp (rev2 y))
      (tlp (rev2 x)))
 (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))

;; Context
C1. (tlp x)
C2. (tlp y)
C3. (endp x)
C4. (tlp (app2 x y))
C5. (tlp (rev2 y))
C6. (tlp (rev2 x))

;; Derived context
D1. (equal x nil)
D2. (tlp (app2 nil y))

;; Goal
(equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x)))

;; Proof
(rev2 (app2 x y))
= {D1}
(rev2 (app2 nil y))
= {Def. app2}
(rev2 (if (endp nil)
          y
	  (cons (first nil) (app2 (rest nil) y))))
= {Ax. endp}
(rev2 (if t
          y
	  (cons (first nil) (app2 (rest nil) y))))
= {if-axioms}
(rev2 y)
= { Lemma app-nil-cons (from lab)}
(app2 (rev2 y) nil)
= { Def rev2 }
(app2 (rev2 y) (rev2 nil))
= { D1 }
(app2 (rev2 y) (rev2 x))

QED
|#

#| 

;; Lemma 1c: rev-app-cons
;; Conjecture:
(implies (tlp x)
 (implies (not (endp x))
   (implies (equal (rev2 (app2 (rest x) y)) (app2 (rev2 y) (rev2 (rest x))))
            (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))))
 
;; Exportation:
(implies (and (tlp x)
              (not (endp x))
              (equal (rev2 (app2 (rest x) y)) (app2 (rev2 y) (rev2 (rest x)))))
         (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))

;; Contract completion:
(implies (and (tlp x)
              (not (endp x))
              (tlp (rest x))
              (tlp y)
              (tlp (rev2 y))
              (tlp (rev2 (rest x)))
              (tlp (app2 (rest x) y))
              (tlp (rev2 x))
              (tlp (app2 x y))
              (equal (rev2 (app2 (rest x) y)) (app2 (rev2 y) (rev2 (rest x)))))
         (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))

;; Context:
C1. (tlp x)
C2. (not (endp x))
C3. (tlp (rest x))
C4. (tlp y)
C5. (tlp (rev2 y))
C6. (tlp (rev2 (rest x)))
C7. (tlp (app2 (rest x) y))
C8. (tlp (rev2 x))
C9. (tlp (app2 x y))
C10. (equal (rev2 (app2 (rest x) y)) (app2 (rev2 y) (rev2 (rest x)))))

;; Derived Context:
D1. (consp x) { C1, C2 }

;; Goal
(equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x)))

;; Proof
(rev2 (app2 x y))
= { Def app2 }
(rev (if (endp x)
       y
       (cons (first x) (app2 (rest x) y))))
= { if-axioms, C3, C4, D1 }
(rev2 (cons (first x) (app2 (rest x) y)))
= { Def rev2 }
(if (endp (cons (first x) (app2 (rest x) y)))
  (cons (first x) (app2 (rest x) y))
  (app2 (rev2 (cdr (cons (first x) (app2 (rest x) y)))) 
        (list (car (cons (first x) (app2 (rest x) y))))))
= { Ax. endp }
(if nil
  (cons (first x) (app2 (rest x) y))
  (app2 (rev2 (cdr (cons (first x) (app2 (rest x) y)))) 
        (list (car (cons (first x) (app2 (rest x) y))))))
= { if-axioms }
(app2 (rev2 (cdr (cons (first x) (app2 (rest x) y)))) 
      (list (car (cons (first x) (app2 (rest x) y)))))
= { Ax. car, Ax. cdr }
(app2 (rev2 (app2 (rest x) y)) (list (first x)))
= { C10 }
(app2 (app2 (rev2 y) (rev2 (rest x))) (list (first x)))
= { Lemma assoc-append }
(app2 (rev2 y) (app2 (rev2 (rest x)) (list (first x))))
= { Def rev2, D1 }
(app2 (rev2 y) (rev2 x))

QED
|#

#| 
Lemma 1: rev-app

We now have each of the three pieces shown

(implies
  (not (tlp x))
  (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))

(implies (tlp x)
  (implies (endp x)
	  (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x)))))

(implies (tlp x)
 (implies (not (endp x))
   (implies (tlp (rest x))
     (equal (rev2 (app2 (rest x) y)) (app2 (rev2 y) (rev2 (rest x))))
   (equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x))))))

With that, we can now state rev-app as a theorem
(equal (rev2 (app2 x y)) (app2 (rev2 y) (rev2 x)))

|#

#| 
Theorem: rev-rev-cons
;; Conjecture:
(implies (and (consp x)
	      (implies (tlp (rest x))
		       (equal (rev2 (rev2 (rest x))) (rest x))))
	 (implies (tlp x)
		  (equal (rev2 (rev2 x)) x)))

;; Exportation:
(implies (and (consp x)
	      (implies (tlp (rest x))
		       (equal (rev2 (rev2 (rest x))) (rest x))))
	 (equal (rev2 (rev2 x)) x))

;; Contract Completion:
(implies (and (consp x)
	      (implies (tlp (rest x))
		       (equal (rev2 (rev2 (rest x))) (rest x)))
	      (tlp x)
	      (tlp (rev2 x))
	      (tlp (rev2 (rest x))))
	 (equal (rev2 (rev2 x)) x))

;; Context
C1. (consp x)
C2. (implies (tlp (rest x)) (equal (rev2 (rev2 (rest x))) (rest x)))
C3. (tlp x)
C4. (tlp (rev2 x))
C5. (tlp (rev2 (rest x)))

;; Derived Context:
D1. (tlp (rest x)) {C1, C3}
D2. (equal (rev2 (rev2 (rest x))) (rest x)) {C2, D1, MP}
D3. (tlp (rev2 (rev2 (rest x)))) {D1, D2}

;; Goal:
(equal (rev2 (rev2 x)) x)

;; Proof:
(rev2 (rev2 x))
= {Def. rev2}
(rev2 (app2 (rev2 (cdr x)) (list (car x))))
= { Lemma rev-app }
(app2 (rev2 (list (car x))) (rev2 (rev2 (cdr x))))
= { D2 }
(app2 (rev2 (list (car x))) (cdr x))
= { Def rev2 }
(app2 (list (car x)) (cdr x))
= { Def app2 }
(cons (first (list (car x))) (app2 (rest (list (car x))) (cdr x)))
= { Ax. car, Ax. cdr }
(cons (car x) (app2 nil (cdr x)))
= { Def app2 }
(cons (car x) (cdr x))
= { Def cons }
x

QED
|# 

#| 

Part III: Undecidability of the Busy Beaver Problem.

You have now seen and understood proofs of the undecidability of the
halting problem. You have encountered this at minimum in the course
textbook, in the "Scooping ..." reading from class, and as discussed
in lecture.

You have also now read and understood a great deal of the proof and
history of the busy beaver problem. You should be able to argue its
undecidability, via an informal proof. In fact, I don't think you
would find that challenging at all.

So, for a little added flavor, you will express a proof of the
undecidabliity of the busy beaver problem in Seussian rhyme, a
la "Scooping." Provide your answer below. You may use slant rhymes if
you need, or regional accents if you
must (e.g. "data"/"later"). Include a title, and your names beneath,
if you please. Please follow your Seussian proof with an explanation
of it in plain English prose. Where not immediately, transparently
obvious point us to what each piece is accomplishing.

|#


#| 

Title: The Busy Beaver Blues
Authors: Sam Pontier

The busy beaver problem is pondered by many fools.
The maximum number of steps in a Turing machine with N rules
Is what this problem seeks to find.
So why has a sequence not yet been defined?

How could we find the busiest beaver of all?
This task, you see, is not so small.
The haulting problem ruins our fun
As we search for an answer, but find none.

Suppose busy beaver of A was something we knew.
We'd run all Turing machines with A rules through.
Some might hault before busy beaver of A,
The rest would never hault, we'd say.

Thus the halting problem would be solved
And our ideas of numbers, completely evolved.
Though we know this can't be, so what does it mean?
Will a solution to the busy beaver problem ever be seen?

Not today, and not by you or me.
It would take a new kind of computer, you see.
Growing faster than any computable sequence known,
The busy beavers problem is undecidable, as I have shown.


Commentary: 

Stanza 1: The busy beaver problem seeks to find the maximum number 
			of steps in non-haulting Turning machines that have N rules.
	
Stanza 2: Introduces the correlation between this problem and the haulting 
			problem (which we know is undecidable).
			
Stanza 3: If we knew the solution of the busy beaver problem for a number A,
			BB(A). We could start all Turing machines with A rules and see 
			how many hault by BB(A). Any machines that have not haulted by 
			then never will, because the maximum number of steps in a haulting 
			machine is BB(A) and these machines will have surpassed that.
			
Stanza 4: Due to the above findings, we see that this would have solved the 
			haulting problem, which we know is undecidable.
			Therefore, contradiction. 
			
Stanza 5: Just restating that the problem is undecidable and serving up a nice
			mic drop to finish it off. QED

|# 
