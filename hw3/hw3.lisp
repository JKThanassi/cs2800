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
  - These commands are simplifying your interactions with ACL2s

  - Do not remove them.

  - To learn more about what they do, see Ch2 found on the course
        readings page
|#

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

; This directive forces ACL2s to generate contract theorems that
; correspond to what we describe in the lecture notes.
(set-defunc-generalize-contract-thm nil)

#| 
https://go.codetogether.com/#/Y8BmvlVZpnzUxEHgeFVDtK/okw20eAhP6i8WQ5bsH3YP3
 It would be a great idea to get started early! This homework picks up
 where the lab left off. In the last lab, we used ACL2s to define the
 syntax and semantics of SRPNEL (Simple Reverse Polish Notation
 Expression Language). In this homework, we will use ACL2s to define
 the syntax and semantics of two RPNELs (Reverse Polish Notation
 Expression Languages), so make sure you have done the lab already.

 A (general) reverse-polish notation expression---an rpnexpr---extends
 srpnexpr with variables. It is one of the following:

- a rational number (we use the builtin type rational)

- a variable (we use the builtin type var)

- a list of the form 
    (- <rpnexpr>)
  where <rpnexpr> is an arithmetic expression

- a list of the form
    (<rpnexpr> <boper> <rpnexpr>)
  where <boper> is one of +, -, or * (the same as SRPNEL)
  and both <rpnexpr>'s are arithmetic expressions.

|#


; Vars are just a restricted set of the symbols. 
; The specifics of which symbols are vars is not all that important
; for our purposes. All we need to know is that vars are symbols and
; they do not include any of the RPNEL operators. Examples of vars include
; symbols such as x, y, z, etc.

;(defdata var (not (oneof 

(check= (varp '-) nil)
(check= (varp '+) nil)
(check= (varp '*) nil)
(check= (varp '/) nil)
(check= (varp 'x) t)
(check= (varp 'x1) t)
(check= (varp 'y) t)

; The defdata-subtype-strict form, below, is used to check that one
; type is a subtype of another type. This is a proof of the claim that
; var is a subtype of symbol.

(defdata-subtype-strict var symbol)

; To see that symbol is not a subtype of var, we can use test? to
; obtain a counterexample to the claim. The must-fail form succeeds
; iff the test? form fails, i.e., it finds a counterexample.

(must-fail (test? (implies (symbolp x)
                           (varp x))))

;;; We use defdata to define boper the binary operators (same as lab):

(defdata boper (enum '(+ - *)))

(check= (boperp '*) t)
(check= (boperp '^) nil)

;;; 1. Use defdata to define rpnexpr with an inductive data definition:

(defdata rpnexpr (oneof rational var `(,rpnexpr -) `(,rpnexpr ,rpnexpr ,boper)))


(check= (rpnexprp '45/3) t)
(check= (rpnexprp '((x y +) (z -) -)) t)
(check= (rpnexprp '(x y z +)) nil)
(check= (rpnexprp '(x + y + z)) nil)

;; 2. What should the following check= forms evaluate to? Make sure
;; you understand each argument that rpnexprp gets for input.

(check= (rpnexprp  12) t)
(check= (rpnexprp '12) t)
(check= (rpnexprp ''12) nil)

(check= (rpnexprp  (- 45)) t)
(check= (rpnexprp '(45 -)) t)
(check= (rpnexprp ''(45 -)) nil)

(check= (rpnexprp  (+ 1/2 45)) t)
(check= (rpnexprp '(+ 1/2 45)) nil)
(check= (rpnexprp ''(1/2 45 +)) nil)

(check= (rpnexprp  (expt 2 3)) t)
(check= (rpnexprp '(expt 2 3)) nil)
(check= (rpnexprp '(2 3 expt)) nil)
(check= (rpnexprp '(2 expt 3)) nil)
(check= (rpnexprp ''(expt 2 3)) nil)

(check= (rpnexprp (car (cons 1 "hi there"))) t)
(check= (rpnexprp `(,(car (cons 1 "hi there")) 12 +)) t) 
(check= (rpnexprp '(+ (car (cons 1 "hi there")) 12)) nil)
(check= (rpnexprp '((car (cons 1 "hi there")) + 12)) nil)
(check= (rpnexprp `(,(car (cons 1 "hi there")) + 12)) nil)

#|

 We have now defined RPNEL expressions in ACL2s. In fact, the use of
 defdata made this pretty easy and gave us a recognizer, rpnexprp, for
 RPNEL expressions. The RPNEL expressions are /still/ not a subset of
 ACL2s expressions. I am not going to ask you to provide an example of
 an RPNEL expression that is not a legal ACL2s expression.

|#

;; 3. Why am I not going to bother asking you to provide an example?
; Since reverse polish notation expects the operator to be at the tail of the list, no RPNEL expression with an operator will be valid LISP. 
; Since LISP expects the first element of a list to be a function it will always fail to evaluate.
 

#| 

Next, we will define the semantics of reverse-polish notation
expressions. The main complication here is extending the language
from lab is to deal with vars. The idea is that to evaluate a var,
we have to know what value it has. We will use an /environment/ to
track and hold the values of variables.

We will represent an environment as an alist from vars to
rationals. When looking up a variable in an alist, we take the
first binding we find with x as the car, as we scan the list from
left to right. For a variable x and an environment ρ (for
"enviρnment"), we say that the value of x in ρ is v (otherwise
written ρ(x) = v) if (x . v) is the first binding that begins with
x.

|#

;; BTW! Where was /this/ when we needed it on last hw!?
;; Sure glad to know it now!!
(defdata env (alistof var rational))

(check= (envp '((x . 1) (y . 1/2))) t)

;; This is nil because (1) and (1/2) are lists, not rationals.
(check= (envp '((x 1) (y 1/2))) nil)

;; 4. Define lookup, a function that given a variable x and an
;; environment ρ, returns the value of x in ρ. Use case-match in your
;; definition.

(definec lookup (x :var p :env) :rational
  (let ((f (first p)))
    (case-match f
                ('nil 1)
                ((!x . val) val)
                (& (lookup x (rest p))))))

#| 


If we look up a var that is not the left-hand side of a binding in
the environment, then we will, by default right now, say that
variable has the value 1. This is a bit like saying that all
variables are pre-initialized to 1.

Remember to use the "template" that defdatas give rise to as per
Section 2.13 of the lecture notes. 

|# 



(check= (lookup 'x '((x . 0) (y . 2))) 0)
(check= (lookup 'y '((x . 0) (y . 2))) 2)
(check= (lookup 'z '((x . 0) (y . 2))) 1)

;; 5. Define rpneval, a function that given an rpnexpr and an
;; environment evaluates the expression, using the environment to
;; determine the values of vars appearing in the expression. Use a
;; case-match in your definition. This should be similar enough to
;; what you did in lab that you /could/ consider copying some of that
;; in and editing it. Remember to use the "template" that defdatas
;; give rise to as per Section 2.13 of the lecture notes.

(definec rpneval (expr :rpnexpr envir :env) :rational
  (case-match expr
              ((exp '-) (- (rpneval exp envir)))
              ((e1 e2 '+) (+ (rpneval e1 envir) (rpneval e2 envir)))
              ((e1 e2 '-) (- (rpneval e1 envir) (rpneval e2 envir)))
              ((e1 e2 '*) (* (rpneval e1 envir) (rpneval e2 envir)))
              (v-or-r (if (rationalp v-or-r) v-or-r (lookup v-or-r envir)))))
                    
#|

 Congratulations! You have formally defined the syntax and semantics
 of RPNEL. The data definition for rpnexpr defines the syntax: it tells
 us what objects in the ACL2s universe are legal rpnexps.
 
|#

(check= (rpneval '((x y +) (z -) -) '((y . 3/2) (z . 1/2)))
        3)
(check= (rpneval '((i -) j *) '()) -1)
(check= (rpneval '(x (s y +) *) '((x . 3) (s . 2))) 9)


#|
 
 Let us unpack the above check= form.

 A: The first argument to rpneval is '((x y +) (z -) -), which is an
 ACL2s expression.

 B: That evaluates to ((x y +) (z -) -), which is not an ACL2s
 expression, but *is* an RPNEL expression; this is what rpneval gets
 as input.

 The function rpneval given us the meaning of this latter
 expression. In fact, the meaning of this latter expression depends on
 the meanings of x, y and z, which are provided by the environment. In
 this instance, the meanings are: 1, 3/2 and 1/2, respectively.
 
|#

;; 6. Specify the following properties using (test? ...) and rpneval.

;; A. A = (- (- A)), in RPNEL, for any rational A.
(test? (implies (and (rationalp a) (envp l)) (equal a (rpneval `( (,a -) -) l))))

;; B. (A B -) = (A (B -) +), in RPNEL, for any rationals A and B.
(test? (implies (and (rationalp a) (rationalp b) (envp l)) (equal (rpneval `(,a ,b -) l) (rpneval `(,a (,b -) +) l))))

;; C. (A (B C +) *) = ((A B *) (A C *) +), in RPNEL, for any rationals A, B & C.
(test? (implies (and (rationalp a) (rationalp b) (rationalp c) (envp l)) 
                (equal (rpneval `(,a (,b ,c +) *) l) (rpneval `((,a ,b *) (,a ,c *) +) l))))

;; D. (E1 E2 -) = (E1 (E2 -) +), in RPNEL, for any rpnexprs E1 and E2.
(test? (implies (and (rpnexprp e1) (rpnexprp e2) (envp l)) 
                (equal (rpneval `(,e1 ,e2 -) l) (rpneval `(,e1 (,e2 -) +) l))))

;; E. (E1 (E2 E3 +) *) = ((E1 E2 *) (E1 E3 *) +), in RPNEL,
;;    for any rpnexpr's E1, E2, E3.
(test? (implies (and (rpnexprp e1) (rpnexprp e2) (rpnexprp e3) (envp l)) 
                (equal (rpneval `(,e1 (,e2 ,e3 +) *) l) (rpneval `((,e1 ,e2 *) (,e1 ,e3 *) +) l))))


;;; RPNPRGM Langauge 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

I believe I heard someone mutter ".. I'm tired of all these
parentheses!" Rejoice! We can fix that! Unlike prefix notation or
infix notation, this post-fix notation behaves in a stack-like
discipline. This means that by using an ancillary stack sort
of "under-the-hood", we can process programs in these languages
without (m)any parentheses. Because for well-formed programs you can
sort of "squint at" the program and put the parentheses back where
they should be. But with our less rigorous syntax, it's now harder to
syntactically distinguish good programs from bad.

|# 

;; 7. Why is it now harder to syntactically distinguish good programs
;; from bad?
; The parens for rpn were explicit about which atoms belonged to which operator. Now it is less clear.

#|

We have grouped the operators variables and rationals together as
just "data". Unary negation is now written "0-".

|# 

(defdata data (oneof (enum '(+ - * 0-)) rational)) ;; var

;; 8. Why is unary "-" (negation) now written "0-"?
;Since the forms of our expressions are not bound by parens we must be explicit about whether an operator is unary or binary. This is why we specify negation as 0-
;; We use defdata to define rpnpgm with an inductive data definition:
(defdata rpnprgm (listof data))

(check= (rpnprgmp '(2 3 +)) t)
(check= (rpnprgmp '(2 3 2 + -)) t)
(check= (rpnprgmp '(2 3 2 + -)) t)

(check= (rpnprgmp '(2 3 4 5 6)) t)

;;; !?

;;; This is believe it or not okay. We can have extra numbers. This is
;;; just the result of a partially completed calculation. If this were
;;; a calculator, you could imagine someone adding the next couple of
;;; characters at the base of the program, so that the full program is
;;; (2 3 4 5 6 - + - -).

;; The answer in that case is 0.


;; But! A new issue has arisen!

(check= (rpnprgmp '(+ + + + +)) t)

#|

It was okay when we had values left over on the stack. But we now also
permit programs for which there aren't *enough* values.

We handle this by introducing a special error value.

We'll now say that an RPNPRGM expression can evaluate to a rational
(if everything goes well), or to the error value (if an error
occurs anywhere in the evaluation of the expression).

|#


(defdata er 'error)
(defdata rat-or-err (oneof rational er))


;; 9. See following the check='s to see examples the idea; add a few
;; of your own.

(check= (rat-or-errp 5)      t)
(check= (rat-or-errp 'error) t)
(check= (rat-or-errp "five") nil)
(check= (rat-or-errp ''error) nil)
(check= (rat-or-errp nil) nil)
(check= (rat-or-errp  (+ 2 3))   t)
(check= (rat-or-errp '(+ 2 3)) nil)
(check= (rat-or-errp '(2 + 3)) nil)
(check= (rat-or-errp '(2 3 +)) nil)



;; 10. Complete the impementation of rpnprgmeval-help. You can omit
;; variables in your implementation, or not. If you add them, remember
;; to reintroduce them into your data definition.



(defdata lor (listof rational))

(definec rpnprgmeval-help (pgm :rpnprgm stk :lor) :rat-or-err
  (case-match pgm
    ('()
     (case-match stk
       ((s1 . &) s1) ;; & serves as a ["wildcard" value](https://en.wikipedia.org/wiki/Wildcard_character).
       (& 'error)))
    ((n . res)
      (if (rationalp n) 
          (rpnprgmeval-help res `(,n . ,stk))
          (let 
            ((stk1 (car stk))
             (stk2 (cadr stk)))
            (if (equal '0- n)
                (if (null stk1)
                    'error
                    (rpnprgmeval-help res `(,(* -1 stk1) . ,(cdr stk))))
                (if (or (null stk1) (null stk2))
                    'error
                    (case-match n
                      ('+ (rpnprgmeval-help res `(,(+ stk1 stk2) . ,(cddr stk))))
                      ('- (rpnprgmeval-help res `(,(- stk2 stk1) . ,(cddr stk))))
                      ('* (rpnprgmeval-help res `(,(* stk1 stk2) . ,(cddr stk))))))))))))

(definec rpnprgmeval (pgm :rpnprgm) :rat-or-err
  (rpnprgmeval-help pgm '()))

(check= (rpnprgmeval '(3 5 * * 2 3 + - *)) 'error)
(check= (rpnprgmeval '(3 5 2 3 + - *)) 0)
(check= (rpnprgmeval '()) 'error)
(check= (rpnprgmeval '(+ * 0- -)) 'error)
(check= (rpnprgmeval '(1 2 3 4 7 9 31 2 99)) 99)
(check= (rpnprgmeval '(5 3 -1 0- + +)) 9)#|ACL2s-ToDo-Line|#



#| 

Now, you should trace the execution of a reasonably large program
in the language of your interpreter from lab.

Then, for that same program, convert any unary "-"s, remove the
inner parentheses, and then trace the run of that program in
rpnprgmeval. 

|#

;; 11. What important difference do you see? Speculate as to why this
;; is.
;;
;; The important difference here is that we are creating our own call stack with the rpnprmgeval fn and 
;; iterating over the list tail-recursivley while the lab version leverages the lisp call stack.
;; 
;; The lab version is a tree structure in which each node is itself a valid expression. This lends itself 
;; towards natural recursion--checking each subtree until we hit a base case. We are able to do this since 
;; we know that any snprnexpr that can be evaluated is, in fact, correctly formed due to the input contracts.
;; 
;; The no paren version is not defined as strictly, and as a consequence, we do not know if the expression 
;; is valid. This means that we have to build up a tree like structure using stack to operate on, 
;; apply functions to that stack when valid, and error when not.
