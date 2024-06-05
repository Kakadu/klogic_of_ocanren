(include "../faster-miniKanren/mk-vicare.scm")
(include "../faster-miniKanren/mk.scm")

(display "Smoke test for default quines with absento\n")
(include "default_quines.scm")

; (myrun 2
;    (lambda (p)
;       (fresh (q r s)
;             (== p `(,q ,r s))
;             (eval-expo q '() `(val_ ,r))
;             (eval-expo r '() `(val_ ,s))
;             (eval-expo s '() `(val_ ,q)))))
(printf "~a\n"
(run 2
   (p)
      (fresh (q r s)
            (== p `(,q ,r ,s))
            (eval-expo q '() r)
            (eval-expo r '() s)
            (eval-expo s '() q))))
(display "Smoke testing of synthesized interpreter\n")
(include "scheme_interpret.scm")
(printf "~a\n"
   (run 2 (q) (evalo2 q '() `(val ,q))))
(printf "~a\n"
(run 2 (p)
      (fresh (q r s)
            (== p `(,q ,r ,s))
            (evalo2 q '() `(val_ ,q))
         ;   (evalo2 r '() `(val_ ,s))
         ;   (evalo2 s '() `(val_ ,q))
         )))