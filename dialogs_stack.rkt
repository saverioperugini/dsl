#lang racket

; atom -> (input, stack) -> result
(define Single
  (lambda (r)
    (lambda (input stack)
      (if (eqv? r (car input))
          (((car stack) 'done) (cdr input) (cdr stack))
          'error))))

(define UpSingle
  (lambda (r)
    (lambda (input stack)
      (if (eqv? r (car input))
          (((cadr stack) ((car stack) 'done)) (cdr input) (cddr stack))
          'error))))

; sub-dialogues -> (input, stack) -> result
(define C
  (lambda ds
    (lambda (input stack)
      (if (null? ds)
          (((car stack) 'done) input (cdr stack))
          ((car ds) input (cons (lambda (d) (apply C (cdr ds)))
                                stack))))))

(define Q
  (lambda ds
    (lambda (input stack)
      (if (null? ds)
          (((car stack) 'done) input (cdr stack))
          ((car ds) input (cons (lambda (d)
                                  (if (eqv? d 'done)
                                      (apply Q (cdr ds))
                                      (apply Q (append (cdr ds) (list d)))))
                                stack))))))

(define W
  (lambda ds
    (lambda (input stack)
      (letrec ((W-help
                (lambda (ds1 ds2)
                  (let ((const (lambda (d)
                                 (if (eqv? d 'done)
                                     (apply W (append ds1 (cdr ds2)))
                                     (apply W (append ds1 (list d) (cdr ds2)))))))
                    (if (null? ds2)
                        'error
                        (let ((result ((car ds2) input (cons const stack))))
                          (if (eqv? result 'error)
                              (W-help (append ds1 (list (car ds2))) (cdr ds2))
                              result)))))))
        (if (null? ds)
            (((car stack) 'done) input (cdr stack))
            (W-help '() ds))))))

(define stage
  (lambda (dialogue input)
    (dialogue input (list (lambda (d) (lambda (in st) in))))))

(define example
  (W (C (UpSingle 'a) (Single 'b)) (C (Single 'x) (Single 'y))))

(stage example '(a b x y))  ; '()
(stage example '(a x y b))  ; '()
(stage example '(x y a b))  ; '()

; all these should give 'error
(stage example '(a b y x))
(stage example '(a y b x))
(stage example '(a y x b))
(stage example '(a x b y))
(stage example '(b a x y))
(stage example '(b a y x))
(stage example '(b y a x))
(stage example '(b y x a))
(stage example '(b x y a))
(stage example '(b x a y))
(stage example '(x a b y))
(stage example '(x a y b))
(stage example '(x y b a))
(stage example '(x b y a))
(stage example '(x b a y))
(stage example '(y a b x))
(stage example '(y a x b))
(stage example '(y x a b))
(stage example '(y x b a))
(stage example '(y b x a))
(stage example '(y b a x))
