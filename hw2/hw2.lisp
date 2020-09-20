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


;; Part I: Defining naturally-recursive functions.

#| 
 For this part, you will complete a set of programming exercises. Give
 yourselves enough time to develop solutions and feel free to define
 helper functions as needed.

 NOTE: We'll scatter properties, checked with THM or TEST?,
 throughout this solution. These are not a required part of the
 homework; we include them as (1) an aid in debugging the code and
 (2) machine-checked documentation. You are of course welcome to start
 to play with them. 

|# 

;;; 1. Define the function DROP-LAST that drops the last element of a
;;; non-empty list.


#|
 Here, we are saying that DROP-LAST produces a list that is
 one element shorter than its input.
|# 

(definec drop-last (l1 :ne-tl) :tl
  (if (= 1 (len l1))
      '()
      (cons (car l1) (drop-last (cdr l1)))))

(check= (drop-last '(x y z)) `(x y))
(check= (drop-last '(x)) '())
(check= (drop-last '(x '(x y z))) '(x))


(thm (implies (ne-tlp xs)
              (= (len (drop-last xs))
                 (- (len xs) 1))))

;;; 2. Define and test a function INSERT-RIGHT that takes two symbols
;;; and a true list and returns a new list with the second symbol
;;; inserted after each occurrence of the first symbol.

(definec insert-right (x :symbol y :symbol l :tl) :tl
  (cond ((lendp l) l)
        ((eq (first l) x)
         (cons x (cons y (insert-right x y (rest l)))))
        ((cons (first l) (insert-right x y (rest l))))))

(check= (insert-right 'x 'y '(x z z x y x)) '(x y z z x y y x y))
(check= (insert-right 'x 'x '(1 2 3 4)) '(1 2 3 4))
(check= (insert-right 'x 'x '()) '())
(thm (implies (and (ne-tlp l) (symbolp x) (symbolp y))
              (if (in x l)
                (> (len (insert-right x y l)) (len l))
                (= (len (insert-right x y l)) (len l)))))

#|

The Lisp function ASSOC takes x, an element of the universe, and l, a
list of pairs. ASSOC returns the first pair in the list whose CAR is
x. If there is no such pair, ASSOC returns nil. ASSOC is built in. You
can try it at the REPL.

This function is named ASSOC because the second data structure is
called an association list. An association list is a (true) list of
pairs of associated values. For example, the following is an
association list:

((A . 5) (B . (1 2)) (C . A))

BTW, you may find the built-in ALIST and ALISTP of use to you. 
 
|# 

;;; 3. Write MY-ASSOC, your own implementation of the lisp ASSOC
;;; function. You should not use ASSOC anywhere in your definition. 

(defdata maybe-pair (oneof nil cons))

(definec my-assoc (x :all l :alist) :maybe-pair
  (cond ((equal (car (car l)) x) (car l))
        ((null (cdr l)) NIL)
        ((my-assoc x (cdr l)))))

(check= (my-assoc 'c '((a . 5) (b . (1 2)) (c . a))) '(c . a))
(check= (my-assoc '(1 2) '((a . 5) ((1 2) . (3 4)))) '((1 2) . (3 4)))
(check= (my-assoc 'y '()) NIL)
(check= (my-assoc '7 '((1 2) (3 4))) NIL)

#| 

The Lisp function REMOVE takes x, an element of the universe, and l, a
list. REMOVE returns a list with, as the name implies, every occurence
of x removed. This function does not "recur deeply", it only operates
at the top level of the list. 

> (remove 'x '(a (x y) b x c x d (x)))
(A (X Y) B C D (X))

You can try it at the REPL. In the followng problem, you should not
use REMOVE.

|# 

;;; 4. Define and test a procedure REMOVE-FIRST that takes a symbol
;;; and a true list and returns a new list with the first occurrence
;;; of the symbol removed.
(definec REMOVE-FIRST (symb :all l :tl) :tl
  (cond ((equal l nil) nil)
        ((equal symb (car l)) (cdr l))
        (t (cons (car l) (REMOVE-FIRST symb (cdr l))))))

(check= (REMOVE-FIRST 'r '(a b r c)) '(a b c))
(check= (REMOVE-FIRST 'r '(a b c)) '(a b c))
(check= (REMOVE-FIRST 'ed '(ed ba by)) '(ba by))
(check= (REMOVE-FIRST 'ed '(ba by ed)) '(ba by))

;;; 5. Define and test a procedure MIRROR that takes a
;;; CONS-constructed binary tree (like those we discussed in lecture)
;;; and recursively exchanges each CAR with its CDR.
(definec MIRROR (tree :cons) :cons
  (cond ((and (not (consp (car tree))) (not (consp (cdr tree))))
         (cons (cdr tree) (car tree)))
        ((not (consp (car tree))) (cons (MIRROR (cdr tree)) (car tree)))
        ((not (consp (cdr tree))) (cons (cdr tree) (MIRROR (car tree))))
        (t (cons (MIRROR (cdr tree)) (MIRROR (car tree))))))

(check= (MIRROR '((g h (a . b) . (c . d)) . (e . f)))
        '((f . e) (((d . c) b . a) . h) . g))

;;; 6. Define a function CONS-CELL-COUNT that counts the number of CONS
;;; cells (i.e. the number of pairs) in a given structure
(definec CONS-CELL-COUNT (tree :all) :nat
  (cond ((not (consp tree)) 0)
        (t (+ 1 (CONS-CELL-COUNT (car tree)) (CONS-CELL-COUNT (cdr tree))))))
 
(check= (cons-cell-count '()) 0)
(check= (cons-cell-count '(a . b)) 1)
(check= (cons-cell-count '(a b)) 2)

#| 

 We can encode natural numbers as backwards-binary true-lists of
 booleans. These are, in the business, called "little-endian" binary
 numbers. E.g. 9 in this representation is '(t nil nil t). This is
 unambiguous because in our notation these numbers never end in nil.

|#

(defdata pos-bb (oneof '(t) (cons t pos-bb) (cons nil pos-bb)))
(defdata bb (oneof nil pos-bb))

;;; 7. Write a function BB-TO-N that takes one of our backward-binary
;;; numbers and returns the nat to which it corresponds. You should
;;; solve this without changing the method's signature. Nor should you
;;; add an accumulator or auxilliary variable in a help method.

(definec bb-to-n (a :bb) :nat
  (cond ((eq NIL a) 0)
        ((equal '(t) a) 1)
        ((car a) (+ 1 (* 2 (bb-to-n (rest a)))))
        ((* 2 (bb-to-n (rest a))))))
         
(check= (bb-to-n NIL) 0)
(check= (bb-to-n '(t)) 1)
(check= (bb-to-n '(nil t)) 2)
(check= (bb-to-n '(t t)) 3)
(check= (bb-to-n '(nil nil t)) 4)
(check= (bb-to-n '(t nil nil t)) 9)

#| 

 Here are some fascinating properties you might want to *prove* for
 such lists

|# 

(test? (implies (pos-bbp x)
              (= (* 2 (bb-to-n x)) (bb-to-n (cons nil x)))))
(check= (bb-to-n nil) 0)
(check= (bb-to-n '(t)) 1)
(check= (bb-to-n '(nil t)) 2)
(check= (bb-to-n '(t t)) 3)
(check= (bb-to-n '(nil nil t)) 4)
(check= (bb-to-n '(t nil nil t)) 9)

;;; 8. Write a function LIST-INDEX-OF that takes an ACL2 value x, and
;;; a list l containing at least one x, and returns the 0-based index
;;; of the first x in l.

(definec list-index-of (x :atom l :tl) :nat
  :ic (and (tlp l) (atom x) (in x l))
  (cond ((equal x (first l)) 0)
        (t (1+ (list-index-of x (rest l))))))
  
(check= (list-index-of 2 '(2)) 0)
(check= (list-index-of 2 '(2 1)) 0)
(check= (list-index-of 4 '(1 4)) 1)
(check= (list-index-of 7 '(0 7 0 7)) 1)
(check= (list-index-of 9 '(1 2 3 9)) 3)


;;; 9. Write a function ZIP-LISTS that takes two lists l1 and
;;; l2. ZIP-LISTS returns a list formed from pairs of elements taken
;;; from with the car coming from l1 and the cdr coming from l2. If
;;; the lists are of uneven length, then drop the tail of the longer
;;; one.


(definec zip-lists (l1 :tl l2 :tl) :alist
  (if (not (or (lendp l1) (lendp l2)))
    (cons (cons (first l1) (first l2)) (zip-lists (rest l1) (rest l2)))
    '()))

(check= (zip-lists '(1 3 5) '(2 4 6)) '((1 . 2) (3 . 4) (5 . 6)))
(check= (zip-lists '() '()) '())
(check= (zip-lists '(1 2) '()) '())
(check= (zip-lists '(nil nil nil) '(t 3 'orange t t)) 
        '((nil . t) (nil . 3) (nil . 'orange)))
(test? (implies (and (tlp l1) (tlp l2))
                (= (len (zip-lists l1 l2)) (min (len l1) (len l2)))))


#| 

  We will do this one in program mode. Then, we will go back to logic
  mode. The termination arguments for this are tricky! Really, it's
  not the function that's tricky: as written, it's just /not/
  guaranteed to terminate! Rather, what's tricky is describing the
  subset of alists on which it *is* guaranteed to terminate.

|#

:program

;;; 10. Write a function WALK-SYMBOL that takes either an atom (almost
;;; always a symbol) and an association list s. Your function should
;;; walk through s for the value associated with x. If the associated
;;; value is a symbol, it too must be walked in s. If x has no
;;; association, then WALK-SYMBOL should return x.
(definec walk-symbol (sym :symbol als :alist) :all
  (let* 
    (
     (ret-assoc (assoc sym als))
     (ret-car (car ret-assoc))
     (ret-cdr (cdr ret-assoc)))
    (cond 
     ((eql ret-car nil) sym)
     ((symbolp ret-cdr)
      (walk-symbol ret-cdr als))
      (t ret-cdr))
  ))

(check= (walk-symbol 'a '((a . 5))) 5)
(check= (walk-symbol 'a '((b . c) (a . b))) 'c)
(check= (walk-symbol 'a '((a . 5) (b . 6) (c . a))) 5)
(check= (walk-symbol 'c '((a . 5) (b . (a . c)) (c . a))) 5)
(check= (walk-symbol 'b '((a . 5) (b . ((c . a))) (c . a))) '((c . a)))
(check= (walk-symbol 'd '((a . 5) (b . (1 2)) (c . a) (e . c) (d . e))) 5)
(check= (walk-symbol 'd '((a . 5) (b . 6) (c . f) (e . c) (d . e))) 'f)
(check= (walk-symbol 'q '((a . 5) (b . 6) (c . f) (e . c) (d . e))) 'q)

:logic

;;; 11. Write a function UNZIP-LISTS that recursively deconstructs a
;;; list of pairs and returns a list of the cars in order followed by
;;; a list of the cdrs also in order.

(definec unzip-helper (lst :alist acc1 :true-list acc2 :true-list) :true-list
  ( if 
   (eql lst nil) (cons (reverse acc1) (reverse acc2))
   (unzip-helper (cdr lst) (cons (caar lst) acc1) (cons (cdar lst) acc2))))

(definec unzip-lists (lst :alist) :true-list
  (if (lendp lst)
    nil
    (unzip-helper (cdr lst) (list (caar lst)) (list (cdar lst)))
    )
  )

(check= (unzip-lists '((a . b) (c . d) (e . f))) '((a c e) . (b d f)))
(check= (unzip-lists '((()))) '((()) ()))
(check= (unzip-lists nil) nil)
(test? (implies (and (alistp x) 
                (not (equal nil x)))
                (equal (unzip-lists x) (cons (strip-cars x) (strip-cdrs x)))))

(test? (implies (alistp e)
                (equal (let ((v (unzip-lists e)))
                         (zip-lists (car v) (cdr v)))
                       e)))#|ACL2s-ToDo-Line|#


;;; Part II Computational complexity with static & dynamic contract checking

#|

Recall the following definitions from the lecture notes.

(definec listp (l :all) :bool 
  (or (consp l)
      (equal l () )))

(definec endp (l :list) :bool
  (atom l))

(definec true-listp (l :all) :bool
  (if (consp l)
      (true-listp (cdr l))
    (equal l ())))

(definec binary-append (x :tl y :all) :all
  (if (endp x)
      y
    (cons (first x) (binary-append (rest x) y))))

This exercise will require you to use what you learned solving
recurrence relations from discrete.

In this section, we will explore the difference between static and
dynamic type checking.

To answer the above questions, we will assume (just for this exercise)
that the following operations have a cost of 1:

 cons, first, rest, consp, atom, or, equal, not, if

We will also assume for this first set of questions that static
contract checking is used.  With static contract checking, ACL2s
checks that the arguments to the function satisfy their contract only
once, for the top-level call. For example, if you type:

(binary-append '(1 2 3 4) '(5 6))

ACL2s checks that '(1 2 3 4) is a true-list and no other contracts.

Remember also that we want the worst-case complexity.  So if the
function has an if-then-else, you must compute separately the
complexity of the then branch, the else branch, and then take the
worst case (i.e., the maximum), plus the complexity of the if
condition itself.

To get you going, we will give the complexity of listp as an example.
Checking the contract statically takes no time, since the type of

x is :all. 

Independently of the size of x, there are 3 operations: (consp x),
(equal x nil), and the or. So the complexity is O(3)=O(1), that is,
constant time. 

Notice that we want the complexity of the functions assuming that the
top-level checking has been already been done.

Please include in your answer a sufficient explanation of how you
reached that answer.  

|#


#|
;; 12. What is the computational complexity of endp?
O(1)

endp has one operation (atom l), so the complexity is constant = O(1)

;; 13. What is the computational complexity of true-listp?
O(n)

true-listp has three or four operations:
if (1), consp (1), and either true-listp (1) and cdr (1) or equal (1).

The complexity of true-listp in the worst case would perform if, consp, true-listp and cdr on n elements for a list of size n,
So the complexity of true-listp is said to be at most O(4*n) = O(n) 

;; 14. What is the computational complexity of binary-append?
O(n)

In the worst case, binary-append executes 6 operations, if, endp, cons, first, binary-append, rest.
For a list of size n, if, endp, cons, first, and rest will be executed n times, and binary-append will be executed n-1 times, so the
complexity is approximately O(6*n)=O(n).

#| 


One way of implementing dynamic checking is to have every function
dynamically check its input contracts. Think about how you might do
that before reading further. So, the above definitions get transformed
into the following. In essence, we are forcing contract checking to
happen dynamically, during runtime.

(definec listp (x :all) :bool
  (or (consp x)
      (equal x nil)))

(definec endp (x :all) :bool
  (if (listp x)
      (atom x)
    (error)))

(definec true-listp (x :all) :bool
  (if (consp x)
      (true-listp (rest x))
    (equal x nil)))

(definec binary-append (x :tl y :all) :all
  (if (true-listp x)
      (if (endp x)
          y
        (cons (first x) (binary-append (rest x) y)))
    (error)))

Please include in your answer a sufficient explanation of how you
reached that answer.  

|# 

;; 15. What is the computational complexity of the modified listp?
O(1)

There are 3 operations equal, consp, or, which all get executed in the worst case. The complexity
of this function is still constant, as O(3)=O(1)

;; 16. What is the computational complexity of the modified endp?
O(1)

There are 3 operations in the worst case, if, list and atom. The complexity is O(3) = O(1)

;; 17. What is the computational complexity of the modified true-listp?
O(n)

In the worst case, there are 3 operations for each n in a list of size n: if, consp, and rest, 
as well as a call to true-listp with the list of size n-1, so the complexity is roughly O(4*n)=O(n)

;; 18. What is the computational complexity of the modified binary-append?
O(n^2)

In the worst case, calling binary-append on a list of size n results in 7 operations each run. 6 of these are 
of constant time complexity, and true-listp is of time complexity O(n), so binary-append is of time complexity
O(n*(n + 6)) = O(n^2 + 6n) = O(n^2).
|#