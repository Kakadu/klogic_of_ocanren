(include "../faster-miniKanren/mk-vicare.scm")
(include "../faster-miniKanren/mk.scm")

(display "Smoke test for default quines with absento\n")
(include "default_quines.scm")

(printf "100 quines\n~a\n"
    (myrun 100 (lambda (q) (eval-expo q '() q))))

(printf "15 twines\n~a\n"
    (myrun 15 (lambda (p) (fresh (q r) (== p `(,q ,r)) (eval-expo q '() r) (eval-expo r '() q)))))

(printf "2 thrines\n~a\n"
  (myrun 2 (lambda (p)
    (fresh (q r s) (== p `(,q ,r ,s)) (eval-expo q '() r) (eval-expo r '() s) (eval-expo s '() q)))))
