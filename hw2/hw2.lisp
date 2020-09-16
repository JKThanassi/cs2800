
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

(thm (implies (ne-tlp xs)
              (= (len (drop-last xs))
                 (- (len xs) 1))))


;;; 2. Define and test a function INSERT-RIGHT that takes two symbols
;;; and a true list and returns a new list with the second symbol
;;; inserted after each occurrence of the first symbol.

(check= (insert-right 'x 'y '(x z z x y x)) '(x y z z x y y x y))


#|

The Lisp function ASSOC takes x, an element of the universe, and l, a
list of pairs. ASSOC returns the first pair in the list whose CAR is
x. If there is no such pair, ASSOC returns nil. ASSOC is built in. You
can try it at the REPL.

This function is named ASSOC because the second data structure is
called an association list. An association list is a (true) list of
pairs of associated values. For example, the following is an
association list:

((a . 5) (b . (1 2)) (c . a))
 
|# 

;;; 3. Write MY-ASSOC, your own implementation of the lisp ASSOC
;;; function. You should not use ASSOC anywhere in your definition. 



;;; 4. Define and test a procedure REMOVE-FIRST that takes a symbol
;;; and a true list and returns a new list with the first occurrence
;;; of the symbol removed.



;;; 5. Define and test a procedure MIRROR that takes a
;;; CONS-constructed binary tree (like those we discussed in lecture)
;;; and recursively exchanges each CAR with its CDR.


(check= (mirror '((g h (a . b) . (c . d)) . (e . f)))
	((f . e) (((d . c) b . a) . h) . g))

;;; 6. Define a function CONS-CELL-COUNT that counts the number of CONS
;;; cells (i.e. the number of pairs) in a given structure

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

(thm (implies (pos-bbp x)
              (= (* 2 (bb-to-n x)) (bb-to-n (cons nil x)))))

;;; 8. Write a function LIST-INDEX-OF that takes an ACL2 value x, and
;;; a list l containing at least one x, and returns the 0-based index
;;; of the first x in l.


;;; 9. Write a function ZIP-LISTS that takes two lists l1 and
;;; l2. ZIP-LISTS returns a list formed from pairs of elements taken
;;; from with the car coming from l1 and the cdr coming from l2. If
;;; the lists are of uneven length, then drop the tail of the longer
;;; one.

(test? (implies (and (tlp l1) (tlp l2))
		(= (len (zip-lists l1 l2)) (min (len l1) (len l2)))))


;;; 10. Write a function WALK-SYMBOL that takes a symbol x and an
;;; association list s. Your function should walk through s for the
;;; value associated with x. If the associated value is a symbol, it
;;; too must be walked in s. If x has no association, then WALK-SYMBOL
;;; should return x. 

(check= (walk-symbol 'a '((a . 5))) 5)
(check= (walk-symbol 'a '((b . c) (a . b))) c)
(check= (walk-symbol 'a '((a . 5) (b . 6) (c . a))) 5)
(check= (walk-symbol 'c '((a . 5) (b . (a . c)) (c . a))) 5)
(check= (walk-symbol 'b '((a . 5) (b . ((c . a))) (c . a))) ((c . a)))
(check= (walk-symbol 'd '((a . 5) (b . (1 2)) (c . a) (e . c) (d . e))) 5)
(check= (walk-symbol 'd '((a . 5) (b . 6) (c . f) (e . c) (d . e))) f)

;;; 11. Write a function UNZIP-LISTS that, given two sorted lists of nats
;;; without duplicates, returns a sorted list of nats without
;;; duplicates containing the elements of both lists. 

(check= (unzip-lists '((()))) '((()) ()))

(test? (implies (lopp e)
		(equal (let ((v (unzip-lists e)))
			 (zip-lists (car v) (cdr v)))
		       e)))

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

;; 12. What is the computational complexity of endp?

;; 13. What is the computational complexity of true-listp?

;; 14. What is the computational complexity of binary-append?


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

;; 16. What is the computational complexity of the modified endp?

;; 17. What is the computational complexity of the modified true-listp?

;; 18. What is the computational complexity of the modified binary-append?
