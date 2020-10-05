(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

#| 

This homework is in part a continuation of what we studied in lab this
week. Therefore, you may find it of considerable interest to complete
the lab first, and then return to this homework afterward. Don't sleep
on this one, though.

|# 

#| 

PART I: PROPOSITIONAL LOGIC BASICS
===============================================================================

For each of the following Boolean formulas:

A. Construct the truth table. Create a column for each of the
   forumula's subexpressions. List the formulas' variables in the
   leftmost columns, and list those variables in alphabetical order.

B. Indicate if the formula is (a) valid, (b) unsatisfiable, or (c)
   both satisfiable and falsifiable. 

B2. If you chose (c) also indicate how many assignments satisfy the
   formula.

C. Answer, with "yes" or "no": "Is this a minimal formula for these
   assignments?" Here "a minimal formula" means that no
   propositionally equivalent formula has fewer subformulae. 

C2. If you chose "no", demonstrate this by finding an equivalent
   minimal formula and constructing a truth table for your new
   formula. The final columns of the old and new formulae should be
   identical. If you wind up simplifying away a variable, include it
   in the truth table anyway so that you can compare the new truth
   table with the previous one.

C3. If you chose "no", write a TEST? expression stating that the
   original formula and your new formula are equivalent. This should
   *not* be in a comment. ACL2s includes a decision procedure for
   validity, so you can use it as a SAT/validity solver to check your
   work. (For example, you can use it to check your characterization
   of formulas in part B, above.) Use the ACL2s logical operators for
   your expressions.

 (If you want to also automate the checks for the number of
  subformulae, you would operate over *our* expression language, and
  use `valof` from lec5.lisp, or implement a translator between our
  language and acl2s logic expressions, and show a theorem about how
  they behave wrt one another. We will not do this.)

   Please refer to your lab for a worked-out example.

|# 

;; 1. ((p => q) => (! (p => (! q))))

#|
A:
+----+----+--------+----+---------+------------+------------------------+
| p  | q  | p => q | !q | p => !q | !(p => !q) | (p => q) => !(p => !q) |
+----+----+--------+----+---------+------------+------------------------+
| tt | tt | tt     | ff | ff      | tt         | tt                     |
+----+----+--------+----+---------+------------+------------------------+
| ff | tt | tt     | ff | tt      | ff         | ff                     |
+----+----+--------+----+---------+------------+------------------------+
| tt | ff | ff     | tt | tt      | ff         | tt                     |
+----+----+--------+----+---------+------------+------------------------+
| ff | ff | tt     | tt | tt      | ff         | ff                     |
+----+----+--------+----+---------+------------+------------------------+
B: C, 2 satisfy, 2 fail
C: NO
C2. p
+----+----+----+
| p  | q  | p  |
+----+----+----+
| tt | tt | tt |
+----+----+----+
| ff | tt | ff |
+----+----+----+
| tt | ff | tt |
+----+----+----+
| ff | ff | ff |
+----+----+----+
C3:
|#
(test? (implies (and (booleanp p) (booleanp q))
                (equal p
                       (implies (implies p q)
                                (not (implies p (not q)))))))

;; 2. (((r => q) => r) => r)

#|
A:
+----+----+--------+---------------+----------------------+
| r  | q  | r => q | (r => q) => r | ((r => q) => r) => r |
+----+----+--------+---------------+----------------------+
| tt | tt | tt     | tt            | tt                   |
+----+----+--------+---------------+----------------------+
| ff | tt | tt     | ff            | tt                   |
+----+----+--------+---------------+----------------------+
| tt | ff | ff     | tt            | tt                   |
+----+----+--------+---------------+----------------------+
| ff | ff | tt     | ff            | tt                   |
+----+----+--------+---------------+----------------------+
B: A, VALID
C: NO
C2. tt
+----+----+--------+---------------+----------------------+----+
| r  | q  | r => q | (r => q) => r | ((r => q) => r) => r | tt |
+----+----+--------+---------------+----------------------+----+
| tt | tt | tt     | tt            | tt                   | tt |
+----+----+--------+---------------+----------------------+----+
| ff | tt | tt     | ff            | tt                   | tt |
+----+----+--------+---------------+----------------------+----+
| tt | ff | ff     | tt            | tt                   | tt |
+----+----+--------+---------------+----------------------+----+
| ff | ff | tt     | ff            | tt                   | tt |
+----+----+--------+---------------+----------------------+----+
C3:
|#
(test? (implies (and (booleanp r) (booleanp q))
                (equal T 
                       (implies (implies (implies r q) r) r))))


;; 3. ((r => (! q)) => (q => (! q)))

#|
A:
+----+----+----+---------+---------+------------------------+
| r  | q  | !q | r => !q | q => !q | (r => !q) => (q => !q) |
+----+----+----+---------+---------+------------------------+
| tt | tt | ff | ff      | ff      | tt                     |
+----+----+----+---------+---------+------------------------+
| ff | tt | ff | tt      | ff      | ff                     |
+----+----+----+---------+---------+------------------------+
| tt | ff | tt | tt      | tt      | tt                     |
+----+----+----+---------+---------+------------------------+
| ff | ff | tt | tt      | tt      | tt                     |
+----+----+----+---------+---------+------------------------+
B: C, 3 satisfy, 1 fails
C: NO
C2: q => r
+----+----+----------+
| r  | q  | (q => r) |
+----+----+----------+
| tt | tt |    tt    |
+----+----+----------+
| ff | tt |    ff    |
+----+----+----------+
| tt | ff |    tt    |
+----+----+----------+
| ff | ff |    tt    |
+----+----+----------+

C3:
|#
(test? (implies (and (booleanp r) (booleanp q))
                (equal (implies q r)
                       (implies (implies r (not q))
                                (implies q (not q))))))


#| 
PART II: IN WE RECOGNIZE THE LION BY HIS CLAUSE
===============================================================================

We know that it can be quite complicated to find satisfying
assignments for boolean formulae, or even to know if one exists. In
fact, the boolean satisfiability problem is NP-Complete. This places
it with the hardest of the hard problems in NP. So, we will set our
sights a little lower. We will restrict ourselves to a particular form
of boolean formulae and study if that helps.

We will study here propositional formulae in a form called HSF. HSF
formulae are a special instance of formulae in CNF. The HSF formulae
are, like CNF formulae, a conjunction of disjunctions of literals. In
HSF, each sequence of disjunctions (a sequence of disjunctions is
called a "clause") has at *most* one positive literal (i.e. at *most*
one non-negated propositional variable.) Notice this simplification
removes the boolean constants for truth and falsity themselves.

;; The following are clauses:
|#

'((! C) v A v (! B) v (! D))
'((! C) v (! B) v (! D))
'((! B) v (! D) v (! C))
'((! D) v C)
'(C)

#|

We can simplify the format even more. Since it's logically equivalent,
we will arrange the clause so we list the positive literal at the end,
if the clause contains a positive literal. In fact, for those with a
positive literal, we will write them as implications. A conjunction of
atoms imply one more. E.g., the implication B ^ C ^ D -> A for the
first clause above. 

|#

;; 4. (Offer an explanation, in terms of our propositional
;; equivalences, why or how this transformation is logically sound.)

#|
Given the implication B ^ C ^ D -> A we can break this down into the form shown on line 173:

1. We know that A => B is equivalent to !A v B 
2. If we substitute (B ^ C ^ D) for A and A for B we get:
  ! (B ^ C ^ D) v A
3. Going further, we can replace ! (B ^ C ^ D) with !B v !C v !D
  This yields !B v !C v !D v A which is the original form. 

Thus the two notations are equivalent
|#

#| 

We will, in fact, go a step or two farther. We will instead write our
implications, (and our arrows) backwards! In this syntax, Accessing
the positive literal is simply taking the CAR. 

Since the "antecedents" of these implications are always a sequence of
conjunctions, we shall elide writing out the '&'s and the
parentheses. We will just hold the antecedents in a list. But you and
I will know that the '&'s are there. 

This merely syntactic simplification doesn't make the problem easier,
it just makes our lives easier.

Here is the result of the transformation for 3 of the clauses above.

|#

'(A <= (B C D))
'(C <= (D))
'(C <= ())


#| 

We will simplify further still! Since all clauses *without* a positive
literal are all disjunctions of negations, we don't need to write out
the disjunctions. And in fact, we don't *need* to write out the
negations. As long as we promise to keep track of which kind of clause
is which.

|# 

'(C B D)
'(B D C)

#| 

Further, since all formulae in HSF are conjunctions of HCs, we will
likewise omit writing the '&'s between the clauses. And we will list
separately the clauses with a positive literal and those without. Once
again, this bit of notational housekeeping is just for our piece of
mind.

|# 

'((A <= (B C D))
  (C <= ())
  (C <= (D)))

'((C B D)
  (B D C))

#| 

One final bit of housekeeping to simplify our lives, that you may or
may not have already noticed. We will require that our lists of
clauses, and the lists of negative literals in each clause, are listed
in sorted order, and unique. That is to say, we represent them as
ordered sets.

|#

'((B C D))

;; 4. Your task: implement an efficient (polynomial time) algorithm
;; SATP for deciding the satisfiability of an HSF sentence in our
;; format.
;; JOE will take this

#|

First, let us heavily suggest making use of [the SET library,
implemented with ordered
sets](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=ACL2____STD_F2OSETS).

Secondly, although we do not intend to spoil your fun and excitement
from learning, let us heavily suggest that you digest and entertain
one or both of the algorithms described in [this
paper](https://www.sciencedirect.com/science/article/pii/0743106684900141).

Third, a hint: Sometimes you might need to write a predicate in order
to describe the desired input as an input contract.

|# 

(defdata gc (listof var))
(defdata gcs (listof gc))
(defdata dc `(,var <= ,gc))
(defdata hsf (listof dc))
;;our defined types
(defdata bhf-var `(,var <= ()))
(defdata hc (oneof dc gc))
(defdata he (listof hc))

#| Given some starter code |#
(definec get-unique-vars (prg :he) :gc
  :ic (not (in nil prg))
  (if (endp prg)
      '()
      (let ((fst-prg (first prg)))
        (case-match fst-prg
        ((x '<= nil) (set::mergesort (cons x (get-unique-vars (rest prg)))))
        ((x '<= y) (set::mergesort (append (cons x y) (get-unique-vars (rest prg)))))
        (x (set::mergesort (append x (get-unique-vars (rest prg)))))))))

(check= (get-unique-vars '((p <= (a b c d e))
                (p <= (q r s v))
                (r <= ())
                (r <= (v x))
                (s <= ())
                (s <= (p q))
                (a b))) '(a b c d e p q r s v x))

(definec initialize-alist (vars :gc acc :alist) :alist
  (if (endp vars)
      acc
      (initialize-alist (rest vars)
                        (put-assoc (first vars) nil acc))))

(check= (initialize-alist '(a b c d e f g) nil) '((a) (b) (c) (d) (e) (f) (g)))

(definec init-bhf-vars (prg :he lut :alist) :alist
  (cond 
   ((endp prg) lut)
   ((bhf-varp (first prg)) (init-bhf-vars (rest prg) (put-assoc (caar prg) t lut)))
   (t (init-bhf-vars (rest prg) lut))))

(check= (init-bhf-vars '((a <= ())
                         (b <= ())
                         (c <= ())
                         (p <= (a b c))
                         (q <= (a b c))
                         (r <= (p q)))
                       (initialize-alist 
                        (get-unique-vars '((a <= ())
                                           (b <= ())
                                           (c <= ())
                                           (p <= (a b c))
                                           (q <= (a b c))
                                           (r <= (p q))))
                        '()))
        '((a . t) (b . t) (c . t) (p . nil) (q . nil) (r . nil)))

(definec all-truep (l :gc lookup :alist) :bool
         (if (endp l)
           t
           (and 
             (cdr (assoc (first l) lookup))
             (all-truep (rest l) lookup))))

(check= (all-truep '(a b c) '((a) (b t) (c t))) nil)
(check= (all-truep '(b c) '((a) (b t) (c t))) t)

(definec filter-single-vars (program :hsf) :hsf
         (if (endp program) nil 
           (let ((fst-hsf (first program)))
             (case-match fst-hsf
                         ((& '<= '()) (filter-single-vars (rest program)))
                         (& (cons fst-hsf (filter-single-vars (rest program))))))))

(definec no-bhf-property (prg :hsf) :bool
         (cond 
           ((endp prg) t)
           ((bhf-varp (first prg)) nil) 
           (t (no-bhf-property (rest prg)))))

(check= (filter-single-vars '((a <= ())
                (b <= ())
                (c <= ())
                (p <= (a b c))
                (q <= (a b c))
                (r <= (p q)))) 
        '(
                (p <= (a b c))
                (q <= (a b c))
                (r <= (p q))))

(thm (implies (and (hsfp a)) (no-bhf-property (filter-single-vars a))))

(definec sat-helper-goal (prgm :gcs lut :alist) :bool
  (if (endp prgm) 
    t       
    (let ((nhc (first prgm)))
      (if (all-truep nhc lut)
        nil
        (sat-helper-goal (rest prgm) lut)))))

(defdata hsf-bool-lut `(,hsf ,bool ,alist))
(definec sat-helper-hsf (prgm :hsf working-prgm :hsf lut :alist change :bool) :hsf-bool-lut
  :ic (not (endp lut))
         (if (endp working-prgm) (list prgm change lut)
           (let ((fst-working (first working-prgm)))
             (case-match fst-working
                         ((& '<= '()) (sat-helper-hsf prgm (rest working-prgm) lut change))
                         ((v '<= lov) (if (and (all-truep lov lut) (not (cdr (assoc v lut)))) 
                                        (sat-helper-hsf (remove fst-working prgm :test 'equal) (rest working-prgm) (put-assoc v t lut) t )
                                        (sat-helper-hsf prgm (rest working-prgm) lut change)
                                        ))))))

(definec sat-helper (prgm :hsf goal :gcs lut :alist) :bool
  :ic (and (not (endp lut)) (not (in nil goal)))
  (if (not (endp prgm))
         (let ((result (sat-helper-hsf prgm prgm lut nil)))
           (case-match result
                       ((p t l) (sat-helper p goal l))
                       ((& nil l) (sat-helper-goal goal l))))
  (sat-helper-goal goal lut)))


(definec satp (prg :hsf goal :gcs) :bool
  :ic (and (not (endp prg)) (not (in nil goal)))
         (let ((eqn (append prg goal)))
           (sat-helper (filter-single-vars prg)
                       goal
                       (init-bhf-vars eqn (initialize-alist (get-unique-vars eqn) '())))))

(check= (satp '((r <= ()))
              '((r)))
        'nil)

(check= (satp '((r <= ()))
              '((r)))
        'nil)

(check= (satp '((r <= (s)))
              '((r)))
        't)

(check= (satp '((r <= (s))
                (s <= (r)))
              '((s)))
        t)

(check= (satp '((p <= (a b c d e))
                (p <= (q r s v))
                (r <= ())
                (r <= (v x))
                (s <= ())
                (s <= (p q)))
              '((r s)))
        nil)

(check= (satp '((p <= (a b c))
                (q <= (a b c))
                (r <= (p q)))
              '((r)))
        t)

(check= (satp '((a <= ())
                (b <= ())
                (c <= ())
                (p <= (a b c))
                (q <= (a b c))
                (r <= (p q)))
              '((q) (r)))
        nil)

(check= (satp '((p <= (a b c))
                (q <= (a b c))
                (r <= (p q)))
              '())
        t)

(check= (satp '((b <= ())
                (c <= ())
                (q <= (a b c))
                (r <= (p q)))
              '((q) (r)))
        T)

(check= (satp '((b <= ())
                (c <= ())
                (q <= (a b c))
                (r <= (p q)))
              '((b) (c)))
        NIL)
