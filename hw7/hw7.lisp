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

#| 

A.

B.

|#

;; 3

(definec f3 (x :tl y :tl acc :tl) :tl
  (cond
    ((and (endp x) (endp y)) acc)
    ((endp x) (f3 x (rest y) (cons (first y) acc)))
    ((endp y) (f3 (rest x) y (cons (first x) acc)))
    (t (f3 x nil (f3 nil y acc)))))

#| 

A.

B.

|#

;; 4

(definec f4 (x :tl y :tl acc :tl) :tl
  (cond
    ((and (endp x) (endp y)) acc)
    ((endp x) (f4 x (rest y) (cons (first y) acc)))
    ((endp y) (f4 y x acc))
    (t (f4 x nil (f4 acc nil y)))))

#| 

A.

B.

|#

;; 5

(definec f5 (x :nat l :tl a :all) :all
  (cond
    ((endp l) a)
    ((== x 0) 1)
    ((oddp x) (f5 (1- x) l a))
    ((> x (len l)) (f5 (/ x 2) l x))
    (t (f5 x (rest l) (first l)))))

#| 

A.

B.

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

