; Modified version of the dialog miner

#lang racket

(define-namespace-anchor a)
(define ns (namespace-anchor->namespace a))

;;;*****************************************************************************
;;;
;;;   A suite of helper/utility functions.
;;;
;;;*****************************************************************************

;;; copies a list n times
(define rep-list
  (lambda (n lst)
    (if (= n 0) '()
        (append (list lst) (rep-list (- n 1) lst)))))

;;; appends each list in ls2 to each list in ls1
(define append-all
  (lambda (ls1 ls2)
    (cond
      ((null? ls1)
       ls2)
      
      ((null? ls2)
       ls1)
      
      ((null? (cdr ls1))
       (map append (rep-list (length ls2) (car ls1)) ls2))
      
      (else
       (append (append-all (cons (car ls1) '()) ls2) (append-all (cdr ls1) ls2))))))

;;; returns the first element of ls that is not a list
(define head
  (lambda (ls)
    (if (list? (car ls)) (head (car ls)) (car ls))))

;;; returns the last element of ls that is not a list
(define last
  (lambda (ls)
    (if (null? (cdr ls)) (if (list? (car ls)) (last (car ls)) (car ls))
        (last (cdr ls)))))

;;; mergesort
(define sort
  (lambda (pred? ls)
    (letrec ((MS1 (lambda (ls len)          
                    (cond
                      ((= len 1) (cons (if (list? (car ls)) (sort pred? (car ls)) (car ls)) '()))
                      (else
                       (let ((i (quotient len 2)))         
                         (merge
                          (MS1 ls i)
                          (MS1 (list-tail ls i) (- len i))))))))
             (merge
              (lambda (l1 l2)
                (cond     
                  ((null? l1) l2) 
                  ((null? l2) l1)
                  ((pred? (head l2) (head l1)) (cons (car l2) (merge l1 (cdr l2))))
                  (else (cons (car l1) (merge (cdr l1) l2)))))))
      (if (null? ls) ls (MS1 ls (length ls))))))

;;; converts a list of symbols to a list of strings
(define list-symbol->string
  (lambda (lst)
    (if (symbol? lst) (symbol->string lst)
        (map list-symbol->string lst))))

;;; converts a list of strings to a list of symbols
(define list-string->symbol
  (lambda (lst)
    (if (string? lst) (string->symbol lst)
        (map list-string->symbol lst))))

;;; sorts a list of strings
(define ascending-string-sort (lambda (lst) (sort string<? lst))) 
;;; sorts a list of symbols
(define ascending-sort (lambda (lst) (list-string->symbol (ascending-string-sort(list-symbol->string lst)))))

;;; checks if a is in lat
(define member?
  (lambda (a lat)
    (call/cc
     (lambda (break)
       (letrec ((M (lambda (l)
                     (cond
                       ((null? l) (break #f))
                       ((equal? a (car l)) (break #t))
                       (else (M (cdr l)))))))
         (M lat))))))

;;; ref. Essentials of Programming Languages by 
;;; D.P. Friedman, M. Wand, and C.T. Haynes. 
;;; MIT Press, Cambridge, MA, Second edition, 2001.
;;; Slightly modified to factor out constant parameter predicate?.
(define list-of
   (lambda (predicate?)
      (letrec ((list-of-helper
         (lambda ()
            (lambda (val)
               (or (null? val)
               (and (pair? val)
                     (predicate? (car val))
                     ((list-of-helper) (cdr val))))))))
      (list-of-helper))))

;;; checks that there are no duplicates in a list
(define set?
  (lambda (ls)
    (cond
      ((null? ls) #t) 
      ((null? (cdr ls)) #t)
      ((member? (car ls) (cdr ls)) #f)
      (else (set? (cdr ls))))))

;;; checks that a list contains only sets
(define all-set-elements? (list-of set?))

;;; calculates n!
(define factorial
  (lambda (n)
    (let fact ((i n) (a 1))
      (if (= i 0) a
          (fact (- i 1) (* a i))))))

;;; by definition (inverse-factorial 1) should
;;; equal 0 and 1, but this is a function and hence it can
;;; only output one value and that value is one
(define inverse-factorial
  (lambda (n)
    (let inv-fac ((i 1) (a 1) (x n))
      (cond
        ((= a x) i)
        ((> a x) (- i 1))
        (else (inv-fac (+ i 1) (* (+ i 1) a) x))))))

;;; returns a list of all permutations of the set
(define permutations
  (lambda (set)
    (if (null? set) '(())
        (if (set? set)    
            (flatmap
             (lambda (x)
               (map (lambda (p) (cons x p)) (permutations (remove x set)))) set)
            ; should output an invalid input message here too
            #f))))

(define filter
  (lambda (predicate sequence)
    (cond
      ((null? sequence) '())
      ((predicate (car sequence))
       (cons (car sequence) (filter predicate (cdr sequence))))
      (else (filter predicate (cdr sequence))))))

(define flatmap
  (lambda (proc seq)
    (accumulate append '() (map proc seq))))

(define remove
  (lambda (item sequence)
    (filter
     (lambda (x) (not (equal? x item)))
     sequence)))

(define accumulate
  (lambda (op initial sequence)
    (letrec ((A (lambda (rest)
                  (if (null? rest) initial
                      (op (car rest)
                          (A (cdr rest)))))))
      (A sequence))))

(define postpend
  (lambda (ls item)
    (if (null? ls) (cons item '())
        (cons (car ls) (postpend (cdr ls) item)))))

(define embed
  (lambda (pre-item ls post-item)
    (if (null? ls) (cons pre-item (cons post-item '()) '())
        (postpend (cons pre-item ls) post-item))))

(define all-equal-elements?
  (lambda (ls)
    (cond
      ((null? ls) #t) 
      ((null? (cdr ls)) #t)
      ((equal? (car ls) (cadr ls)) (all-equal-elements? (cdr ls)))
      (else #f))))

(define remove-dups
  (letrec ((member-equal?
            (lambda (a lat)
              (call/cc
               (lambda (break)
                 (letrec ((M (lambda (l)
                               (cond
                                 ((null? l) (break #f))
                                 ((equal? a (car l)) (break #t))
                                 (else (M (cdr l)))))))
                   (M lat)))))))
    (lambda (ls)
      (cond
        ((null? ls) '())
        ((null? (cdr ls)) ls)
        ((member-equal? (car ls) (cdr ls))
         (remove-dups (cdr ls)))
        (else (cons (car ls)
                    (remove-dups (cdr ls))))))))

(define flatten
  (letrec ((f1 (lambda (ls k)
                 (cond
                   ((null? ls) (k ls))
                   ((list? (car ls)) (f1 (cdr ls) (lambda (x) (k (append (flatten (car ls)) x)))))
                   (else (f1 (cdr ls) (lambda (x) (k (cons (car ls) x)))))))))
    (lambda (ls)
      (cond
        ((null? ls) ls)
        (else (f1 ls (lambda (x) x)))))))

(define (foldl func accum lst)
  (if (null? lst)
      accum
      (foldl func (func accum (car lst)) (cdr lst))))

(define consolidate-sub-lists
  (lambda (ls)
    (foldl append '() ls)))

;;; groups items in ls so that eq-func? returns true between
;;; any two items in a group after applying func to them
(define group-by 
  (lambda (func eq-func? ls)
    (letrec ((group-by1
              (lambda (func eq-func? ls groups)
                (if (null? ls) groups
                    (group-by1 func eq-func? (cdr ls) (append-to-group-by func eq-func? (car ls) groups)))))
             (append-to-group-by
              (lambda (func eq-func? item groups)
                (if (null? groups)
                    (cons (cons item '()) '())
                    (if (eq-func? (func item)
                                  (func (caar groups)))
                        (cons (append (car groups) (cons item '())) (cdr groups))
                        (cons (car groups) (append-to-group-by func eq-func? item (cdr groups))))))))
      (group-by1 func eq-func? ls '()))))

;;; author: Jens Axel S?gaard, September 2002
(define (S n m)
  (cond
    ((= m 0)        (if (= n 0) 1 0))
    ((= n 0)        0)
    (else           (+ (* m (S (- n 1) m))
                       (S (- n 1) (- m 1))))))

;;; author: Jens Axel S?gaard, September 2002
(define P
  (lambda (m)
    (letrec ( (P1 (lambda (n)
                    (cond
                      ((> n m) 0)
                      (else (+(* (factorial n) (S m n)) (P1 (+ n 1))))))))
      (P1 1))))

;;; find n such that (P n) <= x < (P (+ n 1))
(define inverse-P
  (lambda (x)
    (letrec ((inverse-P1 (lambda (x n)
                           (if (<= (P n) x)
                               n
                               (inverse-P1 x (- n 1))))))
      (inverse-P1 x 5))))

(define log2
  (lambda (x)
    (floor (/ (log x) (log 2)))))


(define check-groups
  (lambda (ls len)
    (letrec ((check-groups1 (lambda (ls len curr-len)
                              (if (null? ls)
                                  (= len curr-len)
                                  (let ((new-len (+ curr-len (if (string? (caar ls)) 1 (length (car ls))))))
                                    (cond ((= new-len len)
                                           #t)
                                          ((> new-len len)
                                           #f)
                                          (else
                                           (check-groups1 (cdr ls) len new-len))))))))
      (if (null? ls)
          #t
          (and (if (string? (caar ls))
                   (check-groups1 (cdar ls) len 0)
                   (check-groups1 (car ls) len 0))
               (check-groups (cdr ls) len))))))

(define expr-length
  (lambda (expr)
    (if (string? (car expr))
        (expr-length (cdr expr))
        (+ (length (filter (lambda (x) (string? (car x))) expr))
           (length (flatten (filter (lambda (x) (not (string? (car x)))) expr)))))))

;;; returns first n elements of a expr
;;; dialog type is kept and not counted as one of the first n elements
(define expr-head
  (lambda (expr n)
    (letrec ((expr-head1 (lambda (expr n curr-len)
                           (if (null? expr)
                               expr
                               (let ((new-len (+ curr-len (if (string? (caar expr)) 1 (length (car expr))))))
                                 (if (>= new-len n)
                                     (cons (car expr) '())
                                     (cons (car expr) (expr-head1 (cdr expr) n new-len))))))))
      (if (string? (car expr))
          (cons (car expr) (expr-head1 (cdr expr) n 0))
          (expr-head1 expr n 0)))))

;;; drops n elements from the front of the expr
;;; dialog type not included in the count
(define expr-tail
  (lambda (expr n)
    (letrec ((expr-tail1 (lambda (expr n curr-len)
                           (if (null? expr)
                               expr
                               (let ((new-len (+ curr-len (if (string? (caar expr)) 1 (length (car expr))))))
                                 (if (>= new-len n)
                                     (cdr expr)
                                     (expr-tail1 (cdr expr) n new-len)))))))
      (if (string? (car expr))
          (expr-tail1 (cdr expr) n 0)
          (expr-tail1 expr n 0)))))

;;; returns true if expr1 is a permutation of expr2
(define is-expr-permutation?
  (lambda (expr1 expr2)
    (cond
      ((not (equal? (expr-length expr1)
                    (expr-length expr2)))
       #f) ; different lengths
      ((not (equal? (string? (car expr1))
                    (string? (car expr2))))
       #f) ; one is a dialog type, one is an utterance
      ((and (string? (car expr1))
            (not (equal? (car expr1) (car expr2))))
       #f) ; different dialog types
      (else
       (letrec ((is-dialog? (lambda (x) (and (list? x) (string? (car x)))))
                (not-dialog? (lambda (x) (and (list? x) (not (is-dialog? x)))))
                (sub-dialogs (filter is-dialog? expr1))
                (expr-member?
                 (lambda (x expr)
                   (if (null? expr)
                       #f
                       (if (is-expr-permutation? x (car expr))
                           #t
                           (expr-member? x (cdr expr)))))))
         
         (and (eval (cons 'and (map (lambda (x) (expr-member? x (filter is-dialog? expr2))) sub-dialogs)) ns)
              ; all sub-dialogs in expr1 are in expr2
              (equal? (ascending-sort (filter not-dialog? expr2))
                      (ascending-sort (filter not-dialog? expr1)))
              ; remaining utterances are the same
              ))))))

;;; returns true if expr1 and expr2 have the same dialog and utterances
;;; where grouping of utterances does not matter
(define has-same-expr-parts?
  (lambda (expr1 expr2)
    (cond
      ((not (equal? (expr-length expr1)
                    (expr-length expr2)))
       #f) ; different lengths
      ((not (equal? (string? (car expr1))
                    (string? (car expr2))))
       #f) ; one is a dialog type, one is an utterance
      ((and (string? (car expr1))
            (not (equal? (car expr1) (car expr2))))
       #f) ; different dialog types
      (else
       (letrec ((is-dialog? (lambda (x) (and (list? x) (string? (car x)))))
                (not-dialog? (lambda (x) (and (list? x) (not (is-dialog? x)))))
                (sub-dialogs (filter is-dialog? expr1))
                (expr-member?
                 (lambda (x expr)
                   (if (null? expr)
                       #f
                       (if (has-same-expr-parts? x (car expr))
                           #t
                           (expr-member? x (cdr expr)))))))
         (and (eval (cons 'and (map (lambda (x) (expr-member? x (filter is-dialog? expr2))) sub-dialogs)) ns)
              ; all sub-dialogs in expr1 are in expr2
              (equal? (ascending-sort (flatten (filter not-dialog? expr2)))
                      (ascending-sort (flatten (filter not-dialog? expr1))))
              ; remaining utterances are the same
              ))))))

;;; checks that ls contains all permutations of a expr
(define all-expr-permutations?
  (lambda (ls)
    (letrec ((all-expr-permutations1?
              (lambda (ls)
                (cond
                  ((null? ls) #t) 
                  ((null? (cdr ls)) #t)
                  ((is-expr-permutation? (car ls) (cadr ls)) (all-expr-permutations1? (cdr ls)))
                  (else #f)))))
      (if (null? ls) #t
          (if (= (factorial (expr-length (car ls))) (length ls))
              (if (set? ls)
                  (all-expr-permutations1? ls)
                  #f)
              #f)))))

;;; checks that all expr in ls have the same sub-dialogs and utterances
(define all-have-same-expr-parts?
  (lambda (ls)
    (cond
      ((null? ls) #t) 
      ((null? (cdr ls)) #t)
      ((has-same-expr-parts? (car ls) (cadr ls)) (all-have-same-expr-parts? (cdr ls)))
      (else #f))))

;;; flattens utterances but maintains dialog and sub-dialog structure
(define flatten-expr
  (lambda (ls)
    (if (null? ls) ls
        (if (list? (car ls))
            (if (string? (caar ls))
                (append (cons (flatten-expr (car ls)) '()) (flatten-expr (cdr ls)))
                (append (flatten (car ls)) (flatten-expr (cdr ls))))
            (cons (car ls) (flatten-expr (cdr ls)))))))

;;; checks that sub-dialogs and utterances are in the same order
(define same-expr-order?
  (lambda (x y)
    (letrec ((same-expr-order1?
              (lambda (x y)
                (cond
                  ((or (null? x) (null? y))
                   #t)
                  ((equal? (car x) (car y))
                   (same-expr-order1? (cdr x) (cdr y)))
                  (else
                   #f)))))
      (same-expr-order1? (flatten-expr x) (flatten-expr y)))))

;;; checks that all expr in ls have the same order
(define all-same-expr-order?
  (lambda (ls)
    (cond
      ((null? ls) #t) 
      ((null? (cdr ls)) #t)
      ((same-expr-order? (car ls) (cadr ls)) (all-same-expr-order? (cdr ls)))
      (else #f))))

;;;*****************************************************************************
;;;
;;;   Primary functions used to mine expressions, including mine-expr.
;;;
;;;*****************************************************************************

;;; cleans input for mine-expr
(define clean-input
  (lambda (ls)
    (letrec ((strip-SI ; removes leading "C" if present
              (lambda (ls)
                (if (equal? (car ls) "C")
                    (cdr ls)
                    ls)))
             (listify-input ; turns single utterances into lists
              (lambda (ls)
                (if (null? ls) ls
                    (cond
                      ((list? (car ls))
                       (if (string? (caar ls))
                           (cons (listify-input (car ls)) (listify-input (cdr ls)))
                           (cons (car ls) (listify-input (cdr ls)))))
                      ((string? (car ls))
                       (cons (car ls) (listify-input (cdr ls))))
                      (else
                       (cons (cons (car ls) '()) (listify-input (cdr ls)))))))))
      (map (lambda (x) (listify-input (strip-SI x))) ls))))

;;; adds "C" to a expr if necessary
(define close-expr
  (lambda (ls)
    (if (and (> (length ls) 1)
             (not (string? (car ls))))
        (cons (append '("C") ls) '())
        ls)))

;;; cleans output from mine-expr for easier reading
(define clean-output
  (lambda (ls)
    (letrec ((strip-lists ; removes single utterances from list
              (lambda (ls)
                (if (null? ls) ls
                    (if (list? (car ls))
                        (if (= (length (car ls)) 1)
                            (append (car ls) (strip-lists (cdr ls)))
                            (cons (strip-lists (car ls)) (strip-lists (cdr ls))))
                        (cons (car ls) (strip-lists (cdr ls))))))))
      (map strip-lists ls))))

;;; attempts to find a PE* from all the episodes given
(define find-PE
  (lambda (ls expr)
    (let* ((num-eps (length ls))
           (ep-len (expr-length (car ls)))
           (PE-len (inverse-P num-eps))
           (PE-eps (P PE-len))
           (first-PE-len-elements (map (lambda (x) (expr-head x PE-len)) ls)))
      
      (if (and (= num-eps PE-eps)
               (check-groups ls PE-len)
               (set? first-PE-len-elements)
               (all-have-same-expr-parts? first-PE-len-elements)
               (all-equal-elements? (map (lambda (x) (expr-tail x PE-len)) ls)))
          (if (< PE-len ep-len)
              (cons (append expr (cons (cons "PE*" (if (string? (caar ls))
                                                       (ascending-sort (flatten (cdr (expr-head (car ls) PE-len))))
                                                       (ascending-sort (flatten (expr-head (car ls) PE-len))))) '())) (map (lambda (x) (expr-tail x PE-len)) ls))
              (close-expr (append expr (cons (cons "PE*" (if (string? (caar ls))
                                                             (ascending-sort (flatten (cdar ls)))
                                                             (ascending-sort (flatten (car ls))))) '()))))
          '()))))

;;; attempts to find an SPE' from all the episodes given
(define find-SPEprime
  (lambda (ls expr)
    (let* ((num-eps (length ls))
           (ep-len (expr-length (car ls)))
           (SPEprime-len (inverse-factorial num-eps))
           (SPEprime-eps (factorial SPEprime-len))
           (first-SPEprime-len-elements (map (lambda (x) (expr-head x SPEprime-len)) ls)))
      
      (if (and (= num-eps SPEprime-eps)
               (all-expr-permutations? first-SPEprime-len-elements)
               (all-equal-elements? (map (lambda (x) (expr-tail x SPEprime-len)) ls)))
          (if (< SPEprime-len ep-len)
              (cons (append expr (cons (cons "SPE'" (if (string? (caar ls))
                                                        (cdr (expr-head (car ls) SPEprime-len))
                                                        (expr-head (car ls) SPEprime-len))) '())) (map (lambda (x) (expr-tail x SPEprime-len)) ls))
              (close-expr (append expr (cons (cons "SPE'" (if (string? (caar ls))
                                                              (cdar ls)
                                                              (car ls))) '()))))
          '()))))

;;; attempts to find a PFAN* from all the episodes given
(define find-C
  (lambda (ls expr)
    (let* ((num-eps (length ls))
           (ep-len (expr-length (car ls)))
           (C-len (+ (log2 num-eps) 1))
           (C-eps (expt 2 (- C-len 1)))
           (first-C-len-elements (map (lambda (x) (expr-head x C-len)) ls)))
      
      (if (and (= num-eps C-eps)
               (check-groups ls C-len)
               (all-same-expr-order? first-C-len-elements)
               (set? first-C-len-elements)
               (all-equal-elements? (map (lambda (x) (expr-tail x C-len)) ls)))
          (if (< C-len ep-len)
              (cons (append expr (cons (cons "PFAN*" (if (string? (caar ls))
                                                         (flatten (cdr (expr-head (car ls) C-len)))
                                                         (flatten (expr-head (car ls) C-len)))) '())) (map (lambda (x) (expr-tail x C-len)) ls))
              (close-expr (append expr (cons (cons "PFAN*" (if (string? (caar ls))
                                                               (flatten (cdar ls))
                                                               (flatten (car ls)))) '()))))
          '()))))

;;; attempts to find a group containing a PE* of the length given
(define find-PE-group
  (lambda (ls PE-len)
    (let ((num-eps (length ls))
          (PE-eps (P PE-len))
          (groups-PE (group-by (lambda (x) (expr-head x PE-len)) has-same-expr-parts? ls)))
      (if (and (> num-eps PE-eps)
               (> (length groups-PE) 1))
          ;; checks if any of the groups is actually a PE*
          ;; does extra work - can we save the found PE*
          ;; so mine-expr doesn't have to do the checks again?
          (if (eval (cons 'or (map (lambda (group)
                                     (if (= (length group) PE-eps)
                                         (not (null? (find-PE group '())))
                                         #f)) groups-PE)) ns)
              groups-PE
              '())
          '()))))

;;; attempts to find a group containing an SPE' of the length given
(define find-SPEprime-group
  (lambda (ls SPEprime-len)
    (let ((num-eps (length ls))
          (SPEprime-eps (factorial SPEprime-len))
          (groups-SPEprime (group-by (lambda (x) (expr-head x SPEprime-len)) is-expr-permutation? ls)))
      (if (and (> num-eps SPEprime-eps)
               (> (length groups-SPEprime) 1))
          ;; same comment as above
          (if (eval (cons 'or (map (lambda (group)
                                     (if (= (length group) SPEprime-eps)
                                         (not (null? (find-SPEprime group '())))
                                         #f)) groups-SPEprime)) ns)
              groups-SPEprime
              '())
          '()))))

;;; attempts to find a group containing a PFAN* of the length given
(define find-C-group
  (lambda (ls C-len)
    (let ((num-eps (length ls))
          (C-eps (expt 2 (- C-len 1)))
          (groups-C (group-by (lambda (x) (expr-head x C-len)) same-expr-order? ls)))
      (if (and (> num-eps C-eps)
               (> (length groups-C) 1))
          ;; same comment as above
          (if (eval (cons 'or (map (lambda (group)
                                     (if (= (length group) C-eps)
                                         (not (null? (find-C group '())))
                                         #f)) groups-C)) ns)
              groups-C
              '())
          '()))))

(define valid-input?
  (lambda (ls)
    (cond
      ((not (set? ls))
       (begin
         (display "Invalid Input! ")
         (newline) 
         (display "The input must be a set of episodes.")
         (newline)
         #f))
      ((not (all-set-elements? ls))
       (begin
         (display "Invalid Input! ")
         (newline) 
         (display "Each episode must be a set.")
         (newline)
         #f))
      (else
       #t))))

(define mine-expr 
  (lambda (ls)
    (letrec ((mine-expr1 (lambda (llss expr)
      (let* ((ls (remove-dups llss)) (num-eps (length ls)))
        (cond
          ((null? llss) ls)
          ;; either or episode given to begin
          ;; or the remaining is all I or C
          ((= num-eps 1)
            (cond 
              ((null? expr)
                (cond
                  ((string? (caar ls)) (cons (car ls) '()))
                  (else
                    (cond 
                      ((= (length (car ls)) 1) (cons (cons "I" (caar ls)) '()))
                      (else (cons (cons "C" (car ls)) '()))))))
              (else (close-expr (append expr (car ls))))))
           (else (letrec ((ops (list find-PE find-SPEprime find-C))
             ;; need to generate this list based on number of episodes
             (group-ops (list find-PE-group 4 find-C-group 6
               find-SPEprime-group 4 find-C-group 5
               find-PE-group 3 find-C-group 4
               find-SPEprime-group 3 find-C-group 3
               find-PE-group 2 find-SPEprime-group 2 find-C-group 2))
             ;; try to mine a PE*, SPEprime, or PFAN* using all episodes
             (do-ops
               (lambda (op-list)
                 (if (not (null? op-list))
                   (let ((new-expr ((car op-list) ls expr)))
                     (if (null? new-expr)
                       (do-ops (cdr op-list))
                       (if (null? (cdr new-expr))
                         new-expr
                         (mine-expr1 (cdr new-expr) (car new-expr)))))
                   (do-group-ops group-ops))))
             ;; try to mine a grouping that results in a PE*, SPEprime, or PFAN*
             (do-group-ops (lambda (op-list)
               (cond 
                 ((not (null? op-list))
                   (let ((new-groups ((car op-list) ls (cadr op-list))))
                    (cond
                     ((null? new-groups) (do-group-ops (cddr op-list)))
                     (else (consolidate-sub-lists
                      (map (lambda (x) (mine-expr1 x expr)) new-groups))))))
                 (else
                   (cond
                     ((all-equal-elements?
                       (map (lambda (x) (expr-head x 1)) ls))
                         (mine-expr1 (map (lambda (x) (expr-tail x 1)) ls)
                           (append expr (expr-head (car ls) 1))))
                     ;; else group by first item and try again
                     (else (consolidate-sub-lists
                       (map (lambda (x) (mine-expr1 x expr))
                         (group-by (lambda (x) (expr-head x 1))
                           equal? ls))))))))))
             (do-ops ops))))))))
      ;; main body of function
      (cond  
        ((valid-input? ls)
         (let* ((orig-eps (length ls))
           (new-expr (clean-output (mine-expr1 (clean-input ls) '())))
           (new-eps (length new-expr)))
           (cond
             ((< new-eps orig-eps)
              ;; keep going until no more improvement
              (mine-expr new-expr))
             (else
              ;; convert utterances such as (a b) into ("I" a b)
              (let ((utterance-to-I
                (map
                  (lambda (expr)
                    (map
                      (lambda (x)
                        (cond
                          ((and (list? x) (not (string? (car x))) (> (length x) 1))
                            (cons "I" x))
                          (else x))) expr)) new-expr)))
                (cond
                  ((equal? utterance-to-I new-expr) new-expr)
                  (else (mine-expr utterance-to-I))))))))
        (else "invalid-input")))))


(define main
  (lambda ()
    (let ((inp (read)))
      (if (eof-object? inp)
          (display "")
          (begin
            (display (length inp))
            (display ";")
            (display (length (mine-expr inp)))
            (newline)
            (main))))))

(main)