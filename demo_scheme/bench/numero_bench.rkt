#lang racket
(require math/statistics pretty-format benchmark plot/pict)

(require "../../faster-miniKanren/mk.rkt")
(include "../../faster-miniKanren/numbers.scm")

;(define MAX-BYTES (* 4 1000 1000))
;(custodian-limit-memory (current-custodian) MAX-BYTES)
;(pretty-printf " ~a\n" (current-memory-use))

; HEAP default 822,640,848 bytes allocated in the heap
; 1,487,594,288 bytes allocated in the heap
;(pretty-printf "Warmup:\n  ~a\n"
;    (run 1 (p) (*o (build-num 255) (build-num 255) p))
;)

; 863,479,760
;(pretty-printf "Warmup:\n  ~a\n"
;    (run 1 (p) (logo (build-num 243) (build-num 3) p (build-num 0)))
;)
; 1,076,888,032 bytes
;(pretty-printf "~a\n" (run 1 (p) (expo (build-num 3) (build-num 5) p)))
; 1,026,717,712 bytes allocated in the heap
;(pretty-printf "~a\n" (run 1 (p) (expo (build-num 7) (build-num 2) p)))

;(pretty-printf " ~a\n" (current-memory-use))
;(pretty-printf " ~a\n" (dump-memory-stats))
(define repeat 40)

(define results
    (run-benchmarks
        ; operations (whats)
        (list
            ;'mul255x255
            ;'mul127x127 
            'exp3x5
            'log243base3
            ;'exp7x2
            ;'sleepHalf
        )
        ; list of options (hows)
        (list)
        ; to run each benchmark
        (lambda (op)
            (match op
            ['mul255x255 (run 1 (p) (*o (build-num 255) (build-num 255) p))]
            ['mul127x127 (run 1 (p) (*o (build-num 127) (build-num 127) p))]
            ['log243base3 (run 1 (p) (logo (build-num 243) (build-num 3) p (build-num 0)))]
            ['exp3x5 (run 1 (p) (expo (build-num 3) (build-num 5) p))]
            ['exp7x2 (run 1 (p) (expo (build-num 7) (build-num 2) p))]
            ['sleepHalf (sleep 0.5)]
            ))
        ; don't extract time, instead time (run ...)
        #:extract-time 'delta-time
        #:num-trials repeat ; TODO: 40 is better
        #:results-file "numero_bench_racket.sexp"
    ))

; TODO: plot
(for ([i results])
  (pretty-printf "~a: ~a (mean for ~a repeatitions)\n"
    (benchmark-result-name i)
    (mean (benchmark-result-trial-times i))
    repeat
  )
)