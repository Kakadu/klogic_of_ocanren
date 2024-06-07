#lang racket
(require math/statistics
         pretty-format
         benchmark
         plot/pict)

(require "../../faster-miniKanren/mk.rkt")

; (define lookupo
;   (lambda (x env t)
;     (fresh (rest y v)
;            (== `((,y . ,v) . ,rest) env)
;            (conde ((== y x) (== v t)) ((=/= y x) (lookupo x rest t))))))

; (define not-in-envo
;   (lambda (x env)
;     (conde ((fresh (y v rest) (== env `((,y . ,v) . ,rest)) (=/= y x) (not-in-envo x rest)))
;            ((== '() env)))))

; (define proper-listo
;   (lambda (exp env rs)
;     (conde ((== '() exp) (== '() rs))
;            ((fresh (e d t-e t-d)
;                    (== exp `(,e . ,d))
;                    (== rs `(,t-e . ,t-d))
;                    (eval-expo e env `(val_ ,t-e))
;                    (proper-listo d env t-d))))))

; (define eval-expo
;   (lambda (exp env r)
;     (conde ((fresh (t) (== exp `(seq ((symb 'quote) ,t))) (== r `(val_ ,t)) (not-in-envo 'quote env)))
;            ((fresh (es rs)
;                    (== exp `(seq ((symb 'list) . ,es)))
;                    (== r `(val_ (seq ,rs)))
;                    (not-in-envo 'list env)
;                    (proper-listo es env rs)))
;            ;
;            ((fresh (s) (== exp `(symb ,s)) (lookupo s env r)))
;            ((fresh (rator rand x body env^ a)
;                    (== exp `(seq (,rator ,rand)))
;                    (eval-expo rand env a)
;                    (eval-expo rator env `(closure ,x ,body ,env^))
;                    (eval-expo body `((,x . ,a) . ,env^) r)))
;            ((fresh (x body)
;                    (== exp `(seq ((symb 'lambda) (seq ((symb ,x))) ,body)))
;                    (not-in-envo 'lambda env)
;                    (== r `(closure ,x ,body ,env)))))))
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

; (display (myrun 1 (lambda (q) (eval-expo q '() `(val ,q)))))
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
   #:num-trials 10 ; TODO: 40 is better
   #:results-file "quines_bench_racket.sexp"))

; TODO: plot
(for ([i results])
  (pretty-printf "~a: ~a\n" (benchmark-result-name i) (mean (benchmark-result-trial-times i))))
