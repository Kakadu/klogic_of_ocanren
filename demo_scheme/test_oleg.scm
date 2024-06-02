(include "../faster-miniKanren/mk-vicare.scm")
(include "../faster-miniKanren/mk.scm")

(define build-num
  (lambda (n)
    (cond
      ((odd? n)
       (cons 1
         (build-num (quotient (- n 1) 2))))
      ((and (not (zero? n)) (even? n))
       (cons 0
         (build-num (quotient n 2))))
      ((zero? n) '()))))

(include "OlegNumbers.scm")

(printf "~a\n"
  (run 5 (q) (fresh (b) (appendo q b '(1 2 3)))))

(printf "~a\n"
  (run 1 (q) (pluso (build-num 2) (build-num 2) q)))
(printf "~a\n"
  (run 1 (q) (multo (build-num 2) (build-num 3) q)))