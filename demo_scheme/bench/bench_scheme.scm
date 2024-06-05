#lang racket
(require math/statistics
         pretty-format
         benchmark
         plot/pict)

(require "../../faster-miniKanren/mk.rkt")

;(include "../../faster-miniKanren/mk-vicare.scm")
;(include "../../faster-miniKanren/mk.scm")

; (define build-num
;   (lambda (n)
;     (cond
;       ((odd? n)
;        (cons 1
;          (build-num (quotient (- n 1) 2))))
;       ((and (not (zero? n)) (even? n))
;        (cons 0
;          (build-num (quotient n 2))))
;       ((zero? n) '()))))

(include "../scheme_interpret.scm")

(printf "~a\n" (run 5 (q) (evalo q '() '(val ,q))))
(define myrun
  (lambda (n rel)
    (let ([st empty-state])
      (let ([scope (subst-scope (state-S st))])
        (let ([q (var scope)])
          (map (lambda (st0) (let ([st (state-with-scope st0 nonlocal-scope)]) ((reify q) st)))
               (takeMK n ((rel q) st))))))))

(display "Benchmarking...\n")
(define results
  (run-benchmarks
   ; operations (whats)
   (list 'quines100 'twines15 'thrines2 ; 'sleepHalf
         )
   ; list of options (hows)
   (list)
   ; to run each benchmark
   (lambda (op)
     (match op
       ['quines1 (void (myrun 1 (lambda (q) (eval-expo q '() `(val_ ,q)))))]
       ['quines100 (myrun 100 (lambda (q) (eval-expo q '() `(val_ ,q))))]
       ['twines15
        (myrun
         15
         (lambda (p)
           (fresh (q r) (== p `(,q ,r)) (eval-expo q '() `(val_ ,r)) (eval-expo r '() `(val_ ,q)))))]
       ['thrines2
        (myrun 2
               (lambda (p)
                 (fresh (q r s)
                        (== p `(,q ,r s))
                        (eval-expo q '() `(val_ ,r))
                        (eval-expo r '() `(val_ ,s))
                        (eval-expo s '() `(val_ ,q)))))]
       ['sleepHalf (sleep 0.5)]))
   ; don't extract time, instead time (run ...)
   #:extract-time 'delta-time
   #:num-trials 4 ; TODO: 40 is better
   #:results-file "quines_bench_racket.sexp"))

; TODO: plot
(for ([i results])
  (pretty-printf "~a: ~a\n" (benchmark-result-name i) (mean (benchmark-result-trial-times i))))
