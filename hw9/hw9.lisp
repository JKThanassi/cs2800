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
  (if (endp x) (endp y)
	  (and (in (car x) y)
	       (permp (cdr x) 
		   (del (car x) y)))))

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



;; Proof Obligation 2. 
(implies (and (lorp x) (lorp y) (tlp x))
             (implies (endp x) 
                      (permp x (rev2 x))))

;; Proof Obligation 3. 
(implies (and (lorp x) (lorp y) (tlp x))
             (implies (not (endp x))
                      (implies (permp (cdr x) (rev2 (cdr x)))
                               (permp x (rev2 x)))))
