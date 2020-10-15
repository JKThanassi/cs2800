#|

HW 6. Admission, Measures and Totality

|#

#| 
This homework is, at least _morally_, a continuation of your
assignment from lab. So, you oughta start with that and then come here. 

|#

#| 

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


(definec f1 (x :tl y :int) :nat
  (if (endp x)
      (1+ y)
    (1+ (f1 (rest x) y))))

...

(definec f2 (x :tl a :int) :nat
  (if (endp x)
      (* a (1+ a))
    (f2 (rest x) (1+ a))))

...

(definec f3 (x :int l :tl) :pos
  (cond ((endp l) 1)
        ((> 0 x)  (1+ (f3 (len l) l)))
        (t        (1+ (f3 (1- x) (rest l))))))

...

#| 
Part II Weights and Measures

For each of the following functions, write a measure function to
demonstrate that the original function is terminating. After having
that measure function, use equational reasoning to prove the required
claims.

We now deliberately removed our earlier allowances that let us elide
checking function and body contracts. But we now know what to do about
these! We instead add the following! These will help us debug our
measure functions using ACL2s!

|# 

(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-gag-mode nil)
(set-ignore-ok t)

#| 
As per the lecture notes, ACL2s will complain about the definition of
your measure function unless you tell it to ignore arguments you don't
use. It is simpler to tell it all arguments can be ignored, hence
my (set-ignore-ok t) form.

|# 

;; Don't be a Jason! Give /your/ measure functions a good name! 
(definec m (x :tl y :tl) :nat
  (len x))

;; Notice that the measure has to be of the form (if IC (m ...) 0), 
;; not implies, and 0 for the case the contracts don't hold.

(definec app2 (x :tl y :tl) :tl
  (declare (xargs :measure (if (and (tlp y) (tlp x)) (m x y) 0)))
  (if (endp x)
      y
    (cons (first x) (app2 (rest x) y))))

;; 4. stutter

;; A. Define a measure function for this function definition

;; B. Demonstrate via equational reasoning that this is a measure function (do the proofs)

#|  

|# 

;; C. Modify this function definition to include a measure for termination

(definec stutter (ls :tl) :tl
  (if (endp ls)
      ls
    (cons (car ls) (cons (car ls) (stutter (cdr ls))))))

;; 5. e/o?

;; A. Define a measure function for this function definition

;; B. Demonstrate via equational reasoning that this is a measure function (do the proofs)

#|  

|# 

;; C. Modify this function definition to include a measure for
;; termination. You could modify the function definition if you need,
;; but make sure it's equivalent

(definec e/o? (flag :bool n :nat) :bool
  (cond
   (flag
    (cond
     ((zp n) nil)
     (t (e/o? (not flag) (1- n)))))
   (t
    (cond
     ((zp n) t)
     (t (e/o? (not flag) (1- n)))))))

