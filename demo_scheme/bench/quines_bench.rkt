#lang racket
(require math/statistics
         pretty-format
         benchmark
         left-pad
         plot/pict)

(require "../../faster-miniKanren/mk.rkt")
(include "../default_quines.scm")
(include "../scheme_interpret.scm")

; (define run1
;   (lambda (rel)
;     (map (lambda (p) p)
;          (let ([st empty-state])
;            (let ([scope (subst-scope (state-S st))])
;              (let ([q (var scope)])
;                (map (lambda (st0) (let ([st (state-with-scope st0 nonlocal-scope)]) ((reify q) st)))
;                     (takeMK 1 ((rel q) st)))))))))

; default 755,704,976
; 755,833,664
;(pretty-printf "~a\n" (myrun 1 (lambda (q) (eval-expo q '() `(val_ ,q)))))
; 100 quines: 1,142,906,896
;(pretty-printf "~a\n" (myrun 100 (lambda (q) (eval-expo q '() `(val_ ,q)))))
; 15 twines : 1,041,180,816
; (pretty-printf "~a\n" (myrun 15 (lambda (p)
;                             (fresh (q r)
;                                 (== p `(,q ,r))
;                                 (eval-expo q '() `(val_ ,r))
;                                 (eval-expo r '() `(val_ ,q)))
;                         )))
; 2 thrines: 1,093,984,848 bytes
; (pretty-printf "~a\n" (myrun 2 (lambda (p)
;                             (fresh (q r s)
;                                 (== p `(,q ,r s))
;                                 (eval-expo q '() `(val_ ,r))
;                                 (eval-expo r '() `(val_ ,s))
;                                 (eval-expo s '() `(val_ ,q)))
;                         )))

(display "Benchmarking...\n")
(define results
  (run-benchmarks
   ; operations (whats)
   (list 'quines100 'twines15 'thrines2 'quines100_syn 'twines15_syn 'thrines2_syn ; 'sleepHalf
         )
   ; list of options (hows)
   (list)
   ; to run each benchmark
   (lambda (op)
     (match op
       ['quines1 (void (myrun 1 (lambda (q) (eval-expo q '() q))))]
       ;
       ['quines100 (myrun 100 (lambda (q) (eval-expo q '() q)))]
       ['twines15
        (myrun 15 (lambda (p) (fresh (q r) (== p `(,q ,r)) (eval-expo q '() r) (eval-expo r '() q))))]
       ['thrines2
        (myrun 2
               (lambda (p)
                 (fresh (q r s)
                        (== p `(,q ,r s))
                        (eval-expo q '() r)
                        (eval-expo r '() s)
                        (eval-expo s '() q))))]
       ;
       ['quines100_syn (myrun 100 (lambda (q) (evalo2 q '() `(val ,q))))]
       ['twines15_syn
        (myrun 15
               (lambda (p)
                 (fresh (q r) (== p `(,q ,r)) (evalo2 q '() `(val ,r)) (evalo2 r '() `(val ,q)))))]
       ['thrines2_syn
        (myrun 2
               (lambda (p)
                 (fresh (q r s)
                        (== p `(,q ,r s))
                        (evalo2 q '() `(val ,r))
                        (evalo2 r '() `(val ,s))
                        (evalo2 s '() `(val ,q)))))]

       ['sleepHalf (sleep 0.5)]))
   ; don't extract time, instead time (run ...)
   #:extract-time 'delta-time
   #:num-trials 40 ; TODO: 40 is better
   #:results-file "quines_bench_racket.sexp"))

(define (minim lst)
  (foldl
    (lambda (x y) (if (< x y) x y))
    (first lst)
    (rest lst)))
(define (maxim lst)
  (foldl
    (lambda (x y) (if (< x y) y x))
    (first lst)
    (rest lst)))
; (display results)

(pretty-printf "~a & ~a & ~a & ~a \\\n"
  (left-pad "Name" 15)
  (left-pad "Min"  7)
  (left-pad "Mean" 7)
  (left-pad "Max"  7))

(for ([i results])
  (let ([data (benchmark-result-trial-times i)])
  (pretty-printf "~a & ~a & ~a & ~a \\\\\n"
    (left-pad (benchmark-result-name i) 15)
    (left-pad (truncate (minim data)) 7)
    (left-pad (truncate (mean data)) 7)
    (left-pad (truncate (maxim data)) 7))))
