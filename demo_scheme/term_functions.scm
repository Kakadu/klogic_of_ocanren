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

(define three-element-list (lambda (a b c) `(,a ,b ,c)))


(printf "~a\n"
  (run 1 (q) (== q (three-element-list 1 2 3))))

(defrel (mapo f xs ys)
  (conde
    ((== xs '()) (== ys '()))
    ((fresh (h tl temp tl2)
        (== xs `(,h . ,tl))
        (== ys `(,temp . ,tl2))
        (f h temp)
        (mapo f tl tl2)
    ))
  )
)
(defrel (func x y)
  (conde
    ((== x 1) (== y 'one))
    ((== x 2) (== y 'two))
    ((== x 3) (== y 'three)))
)
(printf "~a\n"
  (run 1 (ys) (mapo func '(1 2 3) ys)))

