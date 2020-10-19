; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
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


;;(definec f1 (x :tl y :int) :nat
;;  (if (endp x)
 ;;     (1+ y)
  ;;  (1+ (f1 (rest x) y))))

;; This function is inadmissable by the following counterexample:
;; ((Y -399) (X '(2 1)))

;;(definec f2 (x :tl a :int) :nat
;;  (if (endp x)
;;      (* a (1+ a))
;;    (f2 (rest x) (1+ a))))

;; By the contract of * (multiplication) we know that it is only checking that the inputs are "acl2-numbers"
;; Thus, we can not be certian that any arbitrary arguments to that function will for sure return a natural which violates our output contract.

(definec f3 (x :int l :tl) :pos
  (cond ((endp l) 1)
        ((> 0 x)  (1+ (f3 (len l) l)))
        (t        (1+ (f3 (1- x) (rest l))))))#|ACL2s-ToDo-Line|#


;;(definec m (x :int l :tl) :nat
;;  (if (< x (len l)) (1+ (len l)) (len l)))
;;proof as follows

;;(implies (and (intp x) (tlp l) (not (endp l) (< x (len l))))
;;         (> (m x l) (m x (rest l)))
;;
;; Context:
;; C1. (intp x) 
;; C2. (tlp l) 
;; C3. (not (endp l)) 
;; C4. (< x (len l))

;; Derived Context:
;; D1. (equal (len l) ((+ 1 (len (cdr l))) { def len, C2, if-axioms }
;; D2. (equal (len l) ((+ 1 (len (rest l))))) {substitute cdr for rest}
;; D3. (equal (m x l) (+ (len l) 1)) { Def m, C4, if-axioms }
;; D4. (equal (m x (rest l)) (+ (len rest l) 1)) { Def m, C4, if-axioms }
;;
;; Goal:
;; (> (m x l) (m x (rest l)))
;;
;; Proof:
;; (> (m x l) (m x (rest l))
;; = { D3, D4 }
;; (> (+ (len l) 1) (+ (len (rest l)) 1))
;; = { D2 }
;; (> (+ (+ 1 (len (rest l)) 1) (+ (len (rest l)) 1)))
;; = { arith }
;; (> (+ 2 (len (rest l)) (+ 1 (len (rest l)))))


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
(definec mstutter (ls :tl) :nat
  (len ls))

;; B. Demonstrate via equational reasoning that this is a measure function (do the proofs)

;; Contract Thm
;(thm (implies (tlp ls) (tlp (stutter ls))))

;; Conjecture 1
;(thm (implies (and (tlp ls) (not (endp ls)))
;              (< (mstutter (cdr ls)) (mstutter ls))))

#|
Termination Proof
Conjecture 1:
(implies (and (tlp ls) (not (endp ls)))
              (< (mstutter (cdr ls)) (mstutter ls)))

Context:
C1. (tlp ls)
C2. (not (endp ls))

Goal: (< (mstutter (cdr ls)) (mstutter ls))

Proof:
(< (mstutter (cdr ls)) (mstutter ls))
= { Def mstutter }
(< (len (cdr ls)) (len ls))
= { C2, Def len }
t

QED
|#

;; C. Modify this function definition to include a measure for termination

(definec stutter (ls :tl) :tl
  (declare (xargs :measure (if (tlp ls) (mstutter ls) 0)))
  (if (endp ls)
      ls
    (cons (car ls) (cons (car ls) (stutter (cdr ls))))))

;; 5. e/o?

;; A. Define a measure function for this function definition
(definec me/o? (flag :bool n :nat) :nat
  (if (zp n) 0 (1+ n)))

;; B. Demonstrate via equational reasoning that this is a measure function (do the proofs)
;; Contract Thm
;(thm (implies (and (boolp flag) (natp n))
;              (boolp (e/o? flag n))))

;; Conjecture
;(thm (implies (and (boolp flag) (natp n) (zp n))
;              (= 0 (me/o? flag n))))

;(thm (implies (and (boolp flag) (natp n) (not (zp n)))
;              (< (me/o? flag (1- n)) (me/o? flag n))))

#|
Termination Proof
Conjecture 1:
(implies (and (boolp flag) (natp n) (zp n))
              (= 0 (me/o? flag n)))
              
Context:
C1. (boolp flag)
C2. (natp n)
C3. (zp n)

Goals: (= 0 (me/o? flag n))

Proof:
(= 0 (me/o? flag n))
= { Def me/o? }
(= 0 (if (zp n) 0 (1+ n)))
= { C3, Arithm }
t

Conjecture 2:
(implies (and (boolp flag) (natp n) (not (zp n)))
              (< (me/o? flag (1- n)) (me/o? flag n)))

Context: 
C1. (boolp flag)
C2. (natp n)
C3. (not (zp n))

Goals: (< (me/o? flag (1- n)) (me/o? flag n))

Proof:
(< (me/o? flag (1- n)) (me/o? flag n))
= { Def me/o? }
(< (if (zp (1- n)) 0 (1+ (1- n))) (if (zp n) 0 (1+ n)))
= { Arithm, Substitution }
(< (if (zp (1- n)) 0 n) (if (zp n) 0 (1+ n)))
= { C3 }
(< (if (zp (1- n)) 0 n) (1+ n))
= { Def <, if-axioms }
(if (zp (1- n))
    (< 0 (1+ n))
    (< n (1+ n)))
= { C3, Arithm }
(if (zp (1- n))
    t
    t)
= { if-axioms }
t

QED
|#

;; C. Modify this function definition to include a measure for
;; termination. You could modify the function definition if you need,
;; but make sure it's equivalent

(definec e/o? (flag :bool n :nat) :bool
  (declare (xargs :measure (if (zp n) 0 (1+ n))))
  (cond
   (flag
    (cond
     ((zp n) nil)
     (t (e/o? (not flag) (1- n)))))
   (t
    (cond
     ((zp n) t)
     (t (e/o? (not flag) (1- n)))))))
