#|

HW 5

This homework is a continuation of your assignment from lab. So,
please do start with that and then proceed apace.

|#


#|

NB. As with lab, we have deliberately removed our earlier allowances
that let us elide checking function and body contracts. We now know
what these are and understand them, so let's use this lab and HW to
get more comfortable.

|# 

(defdata
  (expr (oneof var
           rational
           (list 'quote expr)
           (list '* expr expr)
           (list 'let (list (list var expr)) expr))))

#| 

As discussed, our substitution into programs will only apply to free
variable occurrences. For a re-refresher see Ch 4. pp 76-77.

|# 

(definec var-occursp (v :var e :expr) :bool
  (case-match e
              (('* ex1 ex2) (or (var-occursp v ex1) (var-occursp v ex2)))
              (('let ((& ex1)) ex2) (or (var-occursp v ex1) (var-occursp v ex2)))
              (v-or-r (eq v-or-r v)))
  )

;; 1. Define and test a procedure var-occurs-boundp that takes a
;; var and an expr and returns t if that variable occurs bound in
;; the expression, and nil otherwise. Do not use helper procedures
;; except for var-occursp as you defined above. Do not change the
;; method signature.

(definec var-occurs-boundp (v :var e :expr) :bool
(case-match e 
            (('let ((!v &)) ex1) (var-occursp v ex1))
            (('let ((& &)) ex1) (var-occurs-boundp v ex1))
            (& nil)))

(check= (var-occurs-boundp 'x 'x) nil)

(check= (var-occurs-boundp 'x '(let ((x 5)) x)) t)

(check= (var-occurs-boundp 'y '(let ((x 5)) x)) nil)

(check= (var-occurs-boundp 'y '(let ((y 10)) x)) nil)

(check= (var-occurs-boundp 'y '(let ((y 7)) 'y)) nil)

(check= (var-occurs-boundp 'x '(let ((x (let ((x 5))
                                          x)))
                                 (let ((x x))
                                   x)))
        t)

(check= (var-occurs-boundp 'x '(let ((x (* x x)))
                                 (* x x)))
        t)

(check= (var-occurs-boundp 'z '(let ((y (* x w)))
                                 (let ((x x))
                                   (* y z))))
        nil)

(check= (var-occurs-boundp 'z '(let ((y 10))
                                 (let ((z y))
                                   (* y z))))
        t)

;; 2. Define a function unique-free-vars that takes an expr and
;; returns a sorted list of all the variables that occur free in that
;; expression. The list must not contain duplicate variables. Do not
;; use helper procedures and do not change the method signature.


(definec unique-free-vars (e :expr) :tl
(case-match e
              (('* ex1 ex2) (set::mergesort (set::union (set::mergesort (unique-free-vars ex1)) 
                                                        (set::mergesort (unique-free-vars ex2)))))
              (('let ((v ex1)) ex2) (set::mergesort (set::union (set::mergesort (unique-free-vars ex1))
                                                                (set::delete v (set::mergesort (unique-free-vars ex2))))))
              (v-or-r (if (varp v-or-r) (list v-or-r) nil))
))


(check= (unique-free-vars 'x) '(x))
(check= (unique-free-vars ''x) '())
(check= (unique-free-vars '(let ((x 7)) (* x y)))
        '(y))
(check= (unique-free-vars '(let ((x 10))
                             (* (* x y) x)))
        '(y))
(check= (unique-free-vars '(let ((x (* 10 10)))
                             (* (* z y) x)))
        '(y z))
(check= (unique-free-vars '(let ((a 5))
                             (let ((b a))
                               (let ((c b))
                                 (let ((d c))
                                   (let ((e d))
                                     (* (* (* (* a b) c) d) e)))))))
        '())
(check= (unique-free-vars '(let ((x (let ((w 10))
                                      (* x y))))
                             (let ((y x))
                               y)))
        '(x y))
(check= (unique-free-vars '(let ((x (let ((w 5))
                                      (* x y))))
                             (let ((y x))
                               (* x y))))
        '(x y))
(check= (unique-free-vars
         '(let ((x (let ((c 10))
                     (* x (let ((x c))
                            (* x (* e c)))))))
            (* (* x y) e)))
        '(e x y))
(check= (unique-free-vars
         '(let ((c (let ((x 10))
                     (* (* x y) e))))
            (* x (let ((x 15))
                   (* x (* e c))))))
        '(e x y))
(check= (unique-free-vars '(let ((x 5))
                             (let ((y x))
                               (let ((x y))
                                 (let ((y x))
                                   (* (* x y) z))))))
        '(z))


;; 3. Define a function unique-bound-vars that takes an expr and
;; returns a sorted list of all the variables that occur bound in that
;; expression. The list must not contain duplicate variables. Do not
;; use helper procedures except for var-occursp as you defined
;; above. Do not change the method signature.

(definec unique-bound-vars (e :expr) :tl
  (case-match e 
              (('let ((v ex1)) ex2) (set::mergesort 
                                     (set::union 
                                      (set::mergesort (unique-bound-vars ex1)) 
                                      (set::union 
                                       (if (var-occursp v ex2) (set::mergesort (list v)) nil)
                                       (set::mergesort (unique-bound-vars ex2))))))
              (('* ex1 ex2) (set::mergesort (set::union (set::mergesort (unique-bound-vars ex1)) 
                                                        (set::mergesort (unique-bound-vars ex2)))))
              (& nil)))

(check= (unique-bound-vars 'x) '())
(check= (unique-bound-vars '(let ((x 5)) y)) '())
(check= (unique-bound-vars '(let ((x 5)) (* x y)))
        '(x))
(check= (unique-bound-vars '(let ((x 10)) (* (* x y) x)))
        '(x))
(check= (unique-bound-vars '(let ((x 10)) (* (* z y) x)))
        '(x))
(check= (unique-bound-vars '(let ((a 10))
                              (let ((b a))
                                (let ((c b))
                                  (let ((d c))
                                    (let ((e d))
                                      (* (* (* (* a b) c) d) e)))))))
        '(a b c d e))
(check= (unique-bound-vars '(* 4 (let ((x (* 6 (let ((w 10))
                                                 (* x y)))))
                                   (let ((y 10))
                                     y))))
        '(y))
(check= (unique-bound-vars '(let ((x (let ((w x))
                                       (* x y))))
                              (let ((y y))
                                (* x y))))
        '(x y))
(check= (unique-bound-vars '(let ((x (let ((c 'c))
                                       (* x (let ((x x))
                                              (* x (* e c)))))))
                              (* (* x y) e)))
        '(c x))
(check= (unique-bound-vars '(let ((c (let ((x 10))
                                       (* (* x y) e))))
                              (* x (let ((x 10))
                                     (* x (* e c))))))
        '(c x))
(check= (unique-bound-vars '(let ((x 10))
                              (let ((x x))
                                x)))
        '(x))


#| 

PART II: MORE EQUATIONAL REASONING

This too is a continuation from lab. Prove the following related
conjectures. That is, for each of the conjectures below:

1. Perform conjecture contract checking and add hypotheses if
   necessary. Contract completion is the process of adding the minimal
   set of hypotheses needed to guarantee that the input contracts for
   all functions used in the conjecture are satisfied. See the lecture
   notes. Do not add anything else to the conjecture.

2. Determine if the resulting conjecture is valid or not.  If it is
   valid, provide a proof, as outlined in the lecture notes and in
   class. If it is invalid, provide a counterexample. 

See your lab for more explicit instructions. Make sure to follow the
same instructions as in lab when giving proofs. We redefine below the
set of function definitions you can use.

Once again, I cannot /force/ you to, but you should absolutely use
ACL2s to check the conjectures you come up with, and you should use
the [automated proof checker](http://checker.atwalter.com/checker) to
check the proofs up with which you come. 

EDIT. You might /try/ it, but YMMV. 

|#

;;; Function Definitions

(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

(definec in2 (a :all l :tl) :bool
  (if (endp l)
      nil
    (or (== a (first l)) (in2 a (rest l)))))
    
(definec app2 (x :tl y :tl) :tl
  (if (endp x)
      y
    (cons (first x) (app2 (rest x) y))))

(definec rev2 (x :tl) :tl
  (if (endp x)
      x
    (app2 (rev2 (cdr x)) (list (car x)))))


#| 

;; 4. A revv'er-upper

Conjecture 4:
(implies 
        (boolp (boolp (boolp x))) 
        (boolp (boolp x)))
        
Contract Completion
(implies 
        (and 
          (boolp (boolp (boolp x))) 
          (boolp (boolp x)))
        (boolp (boolp x)))

Context:
C1. (boolp (boolp (boolp x)))
C2. (boolp (boolp x))

Proof:

(boolp (boolp x))
= { c2 }
true

QED

proof comment:
By the contract of boolp (boolp x) is always a boolean
By the definition of boolp (boolp (boolp x)) is always true
The implication is always true

;; 5. Prove the following conjecture.

Conjecture 5:
(implies (tlp ls)
  (implies (endp ls)
    (equal (rev2 (rev2 ls)) ls)))
    
Exportation:
(implies (and (tlp ls)
              (endp ls))
    (equal (rev2 (rev2 ls)) ls)))

Context:
C1. (tlp ls)
C2. (endp ls)

Goal: (equal (rev2 (rev2 ls)) ls)

Proof:
(rev2 (rev2 ls))
= { C2, Def rev2 }
(rev2 (ls))
= { C2, Def rev2 }
ls

QED   


#|

PART III: JUST FOR DESSERT

The below is for fun. You are not required to solve this problem. It
is here for those of you who want more. We shall not grade it.

|#

(set-defunc-termination-strictp nil)

;; You will likely need to disable termination checking for this problem. 
;; Think about /why/, when you did not need to do so to solve the earlier problems.
;; For double fun bonus, ofc, try and do it /without/ disabling the termination !!

;; 6. Define and test a procedure var-occurs-bothp that takes a var
;; and an expr and returns t if that variable both occurs free in the
;; expression and occurs bound in the expression, and nil
;; otherwise. Do not change the method signature, but I created another help function. This
;; should not be implemented as two calls to your occurs-free and
;; occurs-bound functions or anything so simple. It ought to look
;; like a recursive function over the data structure, and I leave the structure of said data up to you. 


(definec var-occurs-bothp (v :var e :expr) :bool
  ...)

(check= (var-occurs-bothp 'x 'x)
        nil)

(check= (var-occurs-bothp 'x '(let ((x 7)) x))
        nil)

(check= (var-occurs-both-helperp 'x '(let ((x 7)) x))
   2)

(check= (var-occurs-both-helperp 'x '(* x (let ((x 5)) x)))
        3)

(check= (var-occurs-both-helperp 'x '(let ((x 5)) (* x (let ((x 5)) x))))
        2)

(check= (var-occurs-bothp 'x '(let ((x 5))
               (* x (let ((x 5))
                     x))))
    'nil) 
(check= (var-occurs-bothp 'x '(* x (let ((x 5))
                     x)))
    't)
(check= (var-occurs-bothp 'x '(let ((y 5))
                (* x (let ((x y))
                       x))))
    't)
(check= (var-occurs-bothp 'x '(let ((x 10))
                (let ((x 15))
                  (* x (let ((x 'x))
                     x)))))
    'nil)
(check= (var-occurs-bothp 'x '(let ((x (let ((y 19))
                     y)))
                (let ((x 22))
                  (* x (let ((x 35))
                     x)))))
    'nil)
(check= (var-occurs-bothp 'x '(let ((y 22))
                (let ((x 17))
                  (let ((z (let ((x 44))
                         (* x (let ((x x))
                            x)))))
                    z))))
    'nil)

(check= (var-occurs-bothp 'x '(let ((x x))
                (let ((y y))
                  (let ((x x))
                    (let ((z z))
                      z)))))
    't)

(check= (var-occurs-bothp 'k '(let ((x x))
                (let ((y y))
                  (let ((x x))
                    (let ((z z))
                      z)))))
    'nil)

(check= (var-occurs-bothp 'x '(let ((x (let ((y y))
                     x)))
                (let ((y 15))
                  (let ((x 22))
                    (let ((z (* 5 '10)))
                      (* x z))))))
    't)

|# 
