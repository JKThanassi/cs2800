#lang racket
(require minikanren)
(require rackunit)

#| 

This week we've begun our discussion of relational programming using
miniKanren.  Before you start the assignment, make sure you have
installed faster-minikanren. If you have, then the above should be
hunky dory.

To familiarize yourself with miniKanren, you should review the
commands from the REPL posted to the course website and your notes
from class.

|#


;; Part I

;; Write the answers to the following problems using your knowledge of
;; miniKanren. For each problem, explain how miniKanren arrived at the
;; answer. You will be graded on the quality of your explanation; a
;; full explanation will require several sentences.

;; 1 What is the value of 

(run 2 (q)
  (== 'cat q)
  (conde
    [(conde 
      [(== 'cat q) (== 'horse q)])
     (== 'cat q)]
    [(== q 'cat)]))

'(cat)
#|
We know that the output of `run` is going to be a list, so we just need to evaluate the
`conde` expression to populate the list. The first line, `(== 'cat q)`, introduces a goal that 
unifies the value of `q` to 'cat, and it does so outside the conde expression. Inside the conde,
the first expression is conjunctive between 'cat and 'horse, so q has no possible value. The 
other expression within the `conde` allows q to be 'cat, so the conde overall sets q to 'cat. 
Because both oossible solutions are `cat, our only solution is `(cat).
|#




;; 2 What is the value of

(run 1 (q) 
  (fresh (a b) 
    (== `(,a ,b) q)
    (absento 'tag q)
    (symbolo a)))

'(((_.0 _.1) (=/= ((_.0 tag))) (sym _.0) (absento (tag _.1))))
#|
  This query is requiring that q is a list of two arbitrary values `a` and `b`. The first restriction
  `absento` is requiring that the symbol tag is not present in either `a` or `b`. Secondly we are requiring that `a` is a symbol value.
  So, to correctly create the list we can only have the values _.0 and _.1 where _.0 is not tag, _.0 is a symbol and _.1 is not tag.
|#
;; 3 What do the following miniKanren constraints mean?

;; a. ==
;; == Creates a goal which is a union of two values 

;; b. =/=
;; Creates a goal which succeeds when e1 is not equal to e2

;; c. absento
;; Ensures that a variable does not appear in a term

;; d. numbero
;; Ensures that the variable is of a number type

;; e. symbolo
;; Ensures that the variable is of a symbol type

;; Part II

;; Here are our versions of the Racket procedures ''stutter'',
;; ''reverse'', and ''assoc'':

#| 

(define (stutter ls)
  (match ls
    [`() '()]
    [`(,a . ,d)
     (let [(res (stutter d))]
       `(,a ,a . ,res))]))

;; Unlike Racket's built in version, our version of assoc does not
;; have a case for when x is absent from the list. How might this be
;; advantageous when we move to relational versions?

(define (assoc x ls)
  (match ls
    [`((,a . ,ad) . ,d)
     (cond
       [(equal? a x) `(,a . ,ad)]
       [(not (equal? a x)) (assoc x d)])]))

(define (reverse ls)
  (match ls
    [`() '()]
    [`(,a . ,d)
     (let [(res (reverse d))]
       (append res `(,a)))]))

|#

;; Take ''assoc'', ''reverse'', and ''stutter'', and translate them
;; into the equivalent miniKanren relations (''assoco'', and
;; ''reverseo'', ''stuttero'') and put them here.

;; Remember that you may need to rearrange some of the goals in your
;; relations to ensure termination (and therefore to pass the
;; tests). In general, recursive calls should come at the end of a
;; sequence of goals, while explicit or implicit calls to ''==''
;; should come at the beginning.













;; The below tests are a guide. Your relations might not pass these
;; tests as such----listing goals in a different order may cause the
;; stream to return results in a different order. So it is possible
;; that your code is correct though the tests fail.

;; If you suspect this is the case, you could use some of the other
;; rackunit functionality to ensure, say, that all our answers are
;; found within in a slightly longer list of answers that your
;; relation produces

(test-equal? "stuttero-inverse-mode"
 (run 1 (q) (stuttero q '(1 1 2 2 3 3)))
 '((1 2 3)))

(test-equal? "stuttero-inverse-mode-complete"
 (run* (q) (stuttero q '(1 1 2 2 3 3)))
 '((1 2 3)))

(test-equal? "stuttero-fills-in-pieces"
 (run 1 (q)
   (fresh (a b c d)
     (== q `(,a ,b ,c ,d))
     (stuttero a `(1 ,b ,c 2 3 ,d))))
 '(((1 2 3) 1 2 3)))

(test-equal? "stuttero-fills-in-other-pieces-leaves-others-fresh"
 (run 1 (q)
   (fresh (a b c d)
     (== q `(,a ,b ,c ,d))
     (stuttero `(,b 1) `(,c . ,d))))
 '((_.0 _.1 _.1 (_.1 1 1))))

(test-equal? "stuttero-minimally-instantiates-first-answer"
 (run 1 (q)
   (fresh (e f g)
     (== q `(,e ,f ,g))
     (stuttero `(,e . ,f) g)))
 '((_.0 () (_.0 _.0))))

(test-equal? "stuttero-minimally-instantiates-first-two-answers"
 (run 2 (q)
   (fresh (e f g)
     (== q `(,e ,f ,g))
     (stuttero `(,e . ,f) g)))
 '((_.0 () (_.0 _.0)) (_.0 (_.1) (_.0 _.0 _.1 _.1))))

(test-equal? "assoco-requires-membership"
 (run* (q) (assoco 'x '() q))
 '())

(test-equal? "assoco-properly-looks-up"
 (run* (q) (assoco 'x '((x . 5)) q))
 '((x . 5)))

(test-equal? "assoco-recurs-appropriately"
 (run* (q) (assoco 'x '((y . 6) (x . 5)) q))
 '((x . 5)))

(test-equal? "assoco-returns-first-element-only"
 (run* (q) (assoco 'x '((x . 6) (x . 5)) q))
 '((x . 6)))

(test-equal? "assoco-runs-in-check-mode"
 (run* (q) (assoco 'x '((x . 5)) '(x . 5)))
 '(_.0))

(test-equal? "assoco-recurs-in-check-mode"
 (run* (q) (assoco 'x '((x . 6) (x . 5)) '(x . 6)))
 '(_.0))

(test-equal? "shadowing-makes-assoco-fail"
 (run* (q) (assoco 'x '((x . 6) (x . 5)) '(x . 5)))
 '())

(test-equal? "irrelevant-what-follows-successful-lookup"
 (run* (q) (assoco 'x '((x . 6) . ,q) '(x . 6)))
 '(_.0))

(test-equal? "generate-some-alists-with-a-given-pair"
 (run 4 (q) (assoco 'x q '(x . 5)))
 '(((x . 5) . _.0)
   (((_.0 . _.1) (x . 5) . _.2) (=/= ((_.0 x))))
   (((_.0 . _.1) (_.2 . _.3) (x . 5) . _.4) (=/= ((_.0 x)) ((_.2 x))))
   (((_.0 . _.1) (_.2 . _.3) (_.4 . _.5) (x . 5) . _.6)
    (=/= ((_.0 x)) ((_.2 x)) ((_.4 x))))))

(test-equal? "reverseo empty list"
 (run* (q) (reverseo '() q))
 '(()))

(test-equal? "reverseo singleton list"
 (run* (q) (reverseo '(a) q))
 '((a)))

(test-equal? "reverseo non-empty, non-singleton list"
 (run* (q) (reverseo '(a b c d) q))
 '((d c b a)))

(test-equal? "reverse with fresh variable element"
 (run* (q) (fresh (x) (reverseo `(a b ,x c d) q)))
 '((d c _.0 b a)))

(test-equal? "solve reverse with fresh element"
 (run* (x) (reverseo `(a b ,x d) '(d c b a)))
 '(c))

(test-equal? "solve reverse with tail fresh"
 (run* (x) (reverseo `(a b c d) `(d . ,x)))
 '((c b a)))

(test-equal? "reverseo knows about tree structure"
 (run* (q) (fresh (x) (reverseo `(a b c d) `(d . (,q . ,x)))))
 '(c))

(test-equal? "generating some reverseoed lists"
 (run 10 (q) (fresh (x y) (reverseo x y) (== `(,x ,y) q)))
 '((() ())
   ((_.0) (_.0)) ((_.0 _.1) (_.1 _.0))
   ((_.0 _.1 _.2) (_.2 _.1 _.0))
   ((_.0 _.1 _.2 _.3) (_.3 _.2 _.1 _.0))
   ((_.0 _.1 _.2 _.3 _.4) (_.4 _.3 _.2 _.1 _.0))
   ((_.0 _.1 _.2 _.3 _.4 _.5) (_.5 _.4 _.3 _.2 _.1 _.0))
   ((_.0 _.1 _.2 _.3 _.4 _.5 _.6)
    (_.6 _.5 _.4 _.3 _.2 _.1 _.0))
   ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7)
    (_.7 _.6 _.5 _.4 _.3 _.2 _.1 _.0))
   ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8)
    (_.8 _.7 _.6 _.5 _.4 _.3 _.2 _.1 _.0))))

