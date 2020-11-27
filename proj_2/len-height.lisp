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

(defdata btree (oneof (cons symbol symbol) 
                      (cons btree symbol) 
                      (cons symbol btree) 
                      (cons btree btree)))


(btreep (cons 'cat 'fish)
        )

(btreep (cons (cons 'cat 'fish) 'turtle))
       

(definec height (bt :btree) :nat
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
      (cons (first x) (app2 (rest x) y))))#|ACL2s-ToDo-Line|#



(definec flatten2 (bt :btree) :los 
  (cond
    ((and (symbolp (car bt)) (symbolp (cdr bt))) (list (car bt) (cdr bt)))
    ((and (btreep (car bt)) (symbolp (cdr bt))) (app2 (flatten2 (car bt)) (list (cdr bt))))
    ((and (symbolp (car bt)) (btreep (cdr bt))) (cons (car bt) (flatten2 (cdr bt))))
    ((and (btreep (car bt)) (btreep (cdr bt)))  (app2 (flatten2 (car bt)) (flatten2 (cdr bt))))))

(definec expt2 (n :nat m :nat) :nat
  (cond
    ((zp m) 1)
    (t (* n (expt2 n (- m 1))))))

(thm (implies (and (tlp a) (tlp b)) (equal (app a b) (app2 a b))))
(thm (implies (and (natp a) (natp b)) (equal (expt a b) (expt2 a b))))


(defthm main
  (implies (btreep bt) 
           (<= (len (flatten2 bt)) 
               (expt2 2 (height bt)))))
    
