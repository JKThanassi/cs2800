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

;;(defdata btree (oneof (cons symbol symbol) 
;;                      (cons btree symbol) 
;;                      (cons symbol btree) 
;;                      (cons btree btree)))

(defdata btree (oneof symbol (cons btree btree)))
(defdata branching-btree (cons btree btree))


(branching-btreep (cons 'cat 'fish)
        )

(branching-btreep (cons (cons 'cat 'fish) 'turtle))
       

(definec height (bt :branching-btree) :nat
  (cond 
    ((and (symbolp (car bt)) (symbolp (cdr bt))) 1)
    ((and (btreep (car bt)) (symbolp (cdr bt))) (+ 1 (height (car bt))))
    ((and (symbolp (car bt)) (btreep (cdr bt))) (+ 1 (height (cdr bt))))
    ((and (btreep (car bt)) (btreep (cdr bt)))  (+ 1 (max (height (car bt)) (height (cdr bt)))))
    ))



(defdata los (listof symbol))




 (definec app2 (x :tl y :tl) :tl
    (if (endp x)
        y
      (cons (first x) (app2 (rest x) y))))


(definec flatten2 (bt :branching-btree) :los 
  (cond
    ((and (symbolp (car bt)) (symbolp (cdr bt))) (list (car bt) (cdr bt)))
    ((and (btreep (car bt)) (symbolp (cdr bt))) (app2 (flatten2 (car bt)) (list (cdr bt))))
    ((and (symbolp (car bt)) (btreep (cdr bt))) (cons (car bt) (flatten2 (cdr bt))))
    ((and (btreep (car bt)) (btreep (cdr bt)))  (app2 (flatten2 (car bt)) (flatten2 (cdr bt))))))

(definec my-expt (n :nat m :nat) :nat
  (cond
    ((zp m) 1)
    (t (* n (my-expt n (- m 1))))))


;; This theorem is showing that app2 is associative. That is that itll produce the same result if called like (app2 (app2 x y) z) (app2 x (app2 y z))
(defthm app2-assoc
  (implies (and (tlp x) (tlp y) (tlp z))
           (equal (app2 (app2 x y) z) (app2 x (app2 y z)))))


;; This theorem is showing that the length of the appended list is the sum of the lengths of its arguments 
(defthm len-of-app2
  (implies (and (tlp x) (tlp y))
        (equal (len (app2 x y))
               (+ (len x) (len y)))))

;; This theorem is showing that my-expt follows the arithmetic property of exponents that r^(i+j) is the same as (r^i * r^j)
(defthm exponents-add-myexpta
  (implies (and (natp r) (natp i) (natp j))
  (equal (my-expt r (+ i j))
                       (* (my-expt r i) (my-expt r j)))))


;; This theorem is showing that my-expt follows the arithmetic property of exponents that exponents distribute over multiplication
(defthm distributivity-of-my-expt-over-*
  (implies (and (natp a) (natp b) (natp i))
        (equal (my-expt (* a b) i)
               (* (my-expt a i) (my-expt b i)))))

;; This theorem is showing that my-expt follows the arithmetic property that any base to the 1 power is itself
(defthm my-exp-1-1
  (implies (natp r)
        (equal (my-expt r 1) r)))
(set-gag-mode nil)

;; This shows that the my-expt function is weakly increasing (at least greater than or equal) for any base greater than 1
;;(defthm my-expt-is-weakly-increasing-for-base->-1
;        (implies (and (< 1 r)
;                      (< i j)
;                      (natp r)
;                      (natp i)
;                      (natp j))
;                 (<= (my-expt r i) (my-expt r j))))
(local (include-book "std/basic/inductions" :dir :system))#|ACL2s-ToDo-Line|#


(defthm test (implies (and
               (posp dif)
               (natp i)
               (natp j)
               (posp r)
               (< 1 r)
               (< i j)
               (equal dif (- j i)))
          (< (my-expt r i) (my-expt r j)))
          :hints (("Goal" :induct (acl2::dec-induct dif))))

;; NOT WORKING -- may need sub lemma
(defthm my-expt-is-increasing-for-base->-1
        (implies (and (< 1 r)
                      (< i j)
                      (natp r)
                      (natp i)
                      (natp j))
                 (< (my-expt r i) (my-expt r j)))
        :hints (:functional-instance (:instance p-f (n r) (m i))
                (p natp) (f my-expt))
        )

;; NOT WORKING -- may need sub lemma
(defthm my-exp-multiply
  (implies (and (natp r) (natp i) (natp j))
                 (equal (my-expt (my-expt r i) j)
                        (my-expt r (* i j)))))


;; Main theorem we are trying to prove
;; The conjecture states that the length of a flattened binary tree is less than or equal to 2 raised to the power of the height of the tree.
(defthm main
  (implies (branching-btreep bt) 
           (<= (len (flatten2 bt)) 
               (my-expt 2 (height bt)))))
    
