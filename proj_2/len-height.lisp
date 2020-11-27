
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
      (cons (first x) (app2 (rest x) y))))


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


(defthm main
  (implies (btreep bt) 
           (<= (len (flatten2 bt)) 
               (expt2 2 (height bt)))))
    
