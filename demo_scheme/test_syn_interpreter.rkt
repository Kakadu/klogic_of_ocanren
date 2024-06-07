(include "../faster-miniKanren/mk-vicare.scm")
(include "../faster-miniKanren/mk.scm")

(display "Smoke test for default quines with absento\n")
(include "scheme_interpret.scm")

(printf "100 quine ~a\n" (myrun 100 (lambda (q) (evalo2 q '() `(val ,q)))))

(printf "15 twines ~a\n"
        (myrun 15
               (lambda (p)
                 (fresh (q r) (== p `(,q ,r)) (evalo2 q '() `(val ,r)) (evalo2 r '() `(val ,q))))))

(printf "2 thrines ~a\n"
        (myrun 2
               (lambda (p)
                 (fresh (q r s)
                        (== p `(,q ,r s))
                        (evalo2 q '() `(val ,r))
                        (evalo2 r '() `(val ,s))
                        (evalo2 s '() `(val ,q))))))
