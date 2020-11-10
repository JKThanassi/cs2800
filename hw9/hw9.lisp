#| 

HW 9: The Proof of the Pudding

|#
#| 

Alrighty, I think we're ready for it. In class, we started
proving (permp x (rev2 x)) and I think we are ready to finish it
off. Below are our function definitions. Please bear in mind that, if
you are not careful, this file could become a mess, and you could find
yourself lost in a morass of your own failed attempts and forgotten
lemmata. Please use caution, and clean up after yourself. 

(definec in (a :all L :lor) :bool
  (and (consp L)
       (or (== a (car l))
               (in a (cdr L)))))

(definec del (a :all L :lor) :lor
  (cond 
    ((endp L) L)
    ((== a (car L)) (cdr L))
    (t (cons (car L) (del a (cdr L))))))
        
(definec permp (x :lor y :lor) :bool
  (if (endp x) 
      (endp y)
      (and (in (car x) y)
           (permp (cdr x) (del (car x) y)))))

 (definec app2 (x :tl y :tl) :tl
        (if (endp x)
                y
          (cons (first x) (app2 (rest x) y))))

  (definec rev2 (x :tl) :tl
        (if (endp x)
                x
          (app2 (rev2 (cdr x)) (list (car x)))))

1. Problem 1 and only, the big kahuna. I want you all to prove, soup
to nuts, (permp x (rev2 x)). 

I think I'll start you off with some structure, though. 

;; Conjecture.
(permp x (rev2 x))

;; We will proceed by induction on x. We must show:

P1. (implies (not (and (lorp x) (lorp y) (tlp x))) 
             (permp x (rev2 x)))
P2. (implies (and (lorp x) (lorp y) (tlp x))
             (implies (endp x) 
                      (permp x (rev2 x))))
P3. (implies (and (lorp x) (lorp y) (tlp x))
             (implies (not (endp x))
                      (implies (permp (cdr x) (rev2 (cdr x)))
                               (permp x (rev2 x)))))


;; Proof Obligation 1. 
(implies (not (and (lorp x) (lorp y) (tlp x))) 
             (permp x (rev2 x)))

;; Contract Completion
(implies (permp x (rev2 x))
         (and (lorp x) (lorp y) (tlp x)))

;; Context
C1. (lorp x)
C2. (lorp y)
C3. (tlp x)
C4. (not (and (lorp x) (lorp y) (tlp x)))

;; Derived Context
D1. nil { C1, C2, C3, C4 }

Q.E.D.

;; Proof Obligation 2. 
(implies (and (lorp x) (lorp y) (tlp x))
             (implies (endp x) 
                      (permp x (rev2 x))))

;; Exportation
(implies (and (lorp x) (lorp y) (tlp x) (endp x))
         (permp x (rev2 x)))

;; Context
C1. (tlp x)
C2. (endp x)
C3. (lorp x)
C4. (lorp y)

;; Goal
(permp x (rev2 x))

;; Proof
(permp x (rev2 x))
= { def rev2, if-axioms, C2 }
(permp x x)
= { Def permp, C2, if-axioms }
(endp x)
= { C2 }
true

Q.E.D

;; Proof Obligation 3. 
(implies (and (lorp x) (lorp y) (tlp x))
             (implies (not (endp x))
                      (implies (permp (cdr x) (rev2 (cdr x)))
                               (permp x (rev2 x)))))

;; Exportation
(implies (and (lorp x) 
              (lorp y) 
              (tlp x)
              (not (endp x))
              (permp (cdr x) (rev2 (cdr x))))
         (permp x (rev2 x)))

;; Context
C1. (lorp x) 
C2. (lorp y) 
C3. (tlp x)
C4. (not (endp x))
C5. (permp (cdr x) (rev2 (cdr x)))

;; Goal
(permp x (rev2 x))

;; Proof
(permp x (rev2 x))
= { Def permp }
(if (endp x)
    (endp (rev2 x))
    (and (in (car x) (rev2 x))
         (permp (cdr x) (del (car x) (rev2 x)))))
= { C4, if-axioms }
(and (in (car x) (rev2 x))
     (permp (cdr x) (del (car x) (rev2 x))))
= { Lemma 2 }
(permp (cdr x) (del (car x) (rev2 x)))
= { Lemma 1, C5, Def permp, PL (Transitive) }
true
Q.E.D


;; Lemma 2:
(in (car x) (rev2 x))

;; Proof obligations:
1. 
(implies (not (lorp x))
         (in (car x) (rev2 x)))

2. 
(implies (lorp x)
          (implies (consp x)
                (implies (equal (car x) (car (rev2 x)))
                        (in (car x) (rev2 x)))))

3.
(implies (lorp x)
          (implies (consp x)
                (implies (not (equal (car x) (car (rev2 x))))
                        (implies (in (car x) (rev2 (cdr x)))
                                 (in (car x) (rev2 x))))))

;; Proof Obligation 1
(implies (endp x)
         (in (car x) (rev2 x)))

;; Contract Completion:
(implies (and (endp x) (consp x))
         (in (car x) (rev2 x)))

;; Context:
C1. (endp x)
C2. (consp x)

;; Derived Context:
D1. nil { C1, C2 }
Q.E.D

;; Proof Obligation 2
(implies (lorp x)
          (implies (consp x)
                (implies (equal (car x) (car (rev2 x)))
                        (in (car x) (rev2 x)))))

;; Exportation
(implies (and (lorp x)
              (consp x)
              (equal (car x) (car (rev2 x))))
         (in (car x) (rev2 x)))

;; Context
C1. (lorp x)
C2. (consp x)
C3. (equal (car x) (car (rev2 x)))

;; Derived Context
D1. (consp (rev2 x)) { C2, Def rev2 }

;; Goal
(in (car x) (rev2 x))

;; Proof
(in (car x) (rev2 x))
= { Def in, D1 }
(or (== (car x) (car (rev2 x)))
    (in (car x) (cdr (rev2 x))))
= { C3, PL }
true
Q.E.D

;; Proof Obligation 3
(implies (lorp x)
          (implies (consp x)
                (implies (not (equal (car x) (car (rev2 x))))
                        (implies (in (car x) (rev2 (cdr x)))
                                (in (car x) (rev2 x))))))

;; Exportation
(implies (and (lorp x)
              (consp x)
              (not (equal (car x) (car (rev2 x))))
              (in (car x) (rev2 (cdr x))))
         (in (car x) (rev2 x)))

;; Context
C1. (lorp x)
C2. (consp x)
C3. (not (equal (car x) (car (rev2 x))))
C4. (in (car x) (rev2 (cdr x)))

;; Derived Context
D1. (consp (rev2 x)) { C2, Def rev2 }

;; Goal
(in (car x) (rev2 x))

;; Proof
(in (car x) (rev2 x))
= { Def in, D1, C3 }
(in (car x) (cdr (rev2 x)))
= { C4 }
true
Q.E.D


;; Lemma 1:
(permp (rev2 (cdr x)) (del (car x) (rev2 x)))

;; Proof Obligations:
1. 
(implies (not (and (tlp x)))
         (equal (rev2 (cdr x)) (del (car x) (rev2 x))))

2. 
(implies (tlp x)
        (implies (endp (rev2 x))
                (equal (rev2 (cdr x)) (del (car x) (rev2 x)))))

3. 
(implies (tlp x)
        (implies (not (endp (rev2 x)))
                 (implies (== (car x) (car (rev2 x))))
                          (equal (rev2 (cdr x)) (del (car x) (rev2 x)))))

4. 
(implies (tlp x)
        (implies (not (endp (rev2 x)))
                 (implies (equal (rev2 (cdr (cdr x))) (del (car x) (rev2 (cdr x))))
                          (equal (rev2 (cdr x)) (del (car x) (rev2 x))))))

;; Proof Obligation 1
(implies (not (and (tlp x))) 
        (equal (rev2 (cdr x)) (del (car x) (rev2 x))))

;; Contract Completion
(implies (equal (rev2 (cdr x)) (del (car x) (rev2 x)))
        (tlp x))

;; Context
C1. (not (and (tlp x)))
C2. (tlp x) 

;; Derived Context:
D1. nil { C1, C2 }
Q.E.D.

;; Proof Obligation 2
(implies (tlp x)
        (implies (endp (rev2 x))
                (equal (rev2 (cdr x)) (del (car x) (rev2 x)))))

Exportation:
(implies (and (tlp x) (endp L))
        (equal (rev2 (cdr x)) (del (car x) (rev2 x))))

Context:
C1. (tlp x)
C2. (endp (rev2 x))

Derived Context:
D1. (endp x) { C1, def rev2, if-axioms }
D2. (equal (cdr x) nil) { completion axiom } -- Note: using the completion axiom built into acl2s. See :doc cdr for details
D3. (equal (car x) nil) { completion axiom } -- Note: using the completion axiom built into acl2s. See :doc car for details

Goal:   
(equal (rev2 (cdr x)) (del (car x) (rev2 x)))

Proof:
(equal (rev2 (cdr x)) (del (car x) (rev2 x)))
= { def rev2, D2 }
(equal nil (del (car x) (rev2 x)))
= {  D3, def rev2, if-axioms }
(equal nil (del nil nil))
= { def delete, if-axioms }
(equal nil nil)
=
t
Q.E.D

;; Proof Obligation 3
(implies (tlp x)
        (implies (not (endp (rev2 x)))
                 (implies (== (car x) (car (rev2 x))))
                          (equal (rev2 (cdr x)) (del (car x) (rev2 x)))))

;; Exportation:
(implies (and (tlp x) 
              (not (endp (rev2 x))) 
              (== (car x) (car (rev2 x))))
         (equal (rev2 (cdr x)) (del (car x) (rev2 x))))

;; Context:
C1. (tlp x)
C2. (not (endp (rev2 x)))
C3. (== (car x) (car (rev2 x)))

;; Goal:
(equal (rev2 (cdr x)) (del (car x) (rev2 x)))

;; Proof:
(equal (rev2 (cdr x)) (del (car x) (rev2 x)))
= { def del, C1, C2, C3, if-axioms }
(equal (rev2 (cdr x)) (cdr (rev2 x)))
= { PL }
true
Q.E.D.

;; Proof Obligation 4
(implies (tlp x)
        (implies (not (endp (rev2 x)))
                (equal (rev2 (cdr x)) (del (car x) (rev2 x)))))

;; Exportation:
(implies (and (tlp x) (not (endp (rev2 x))))
        (equal (rev2 (cdr x)) (del (car x) (rev2 x))))

;; Context:
C1. (tlp x)
C2. (not (endp (rev2 x)))
C3. (equal (rev2 (cdr (cdr x))) (del (car x) (rev2 (cdr x)))

;; Derived Context:
D1. (not (endp x)) { C2, def rev2 }

;; Goal: 
(equal (rev2 (cdr x)) (del (car x) (rev2 x)))

;; Proof:
(equal (rev2 (cdr x)) (del (car x) (rev2 x)))
= { def rev2, C2 }
(equal (rev2 (cdr x))
       (del (car x)
            (app2 (rev2 (cdr x)) (list (car x)))))
= { Def app2, del }
(equal (rev2 (cdr x)) (rev2 (cdr x)))
= { PL }
true
Q.E.D.
|#