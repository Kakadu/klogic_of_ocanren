; FUCK

;;; There are 4 relations
; zeroo 162
(define zeroo (lambda (n)
                                                (== n '()))
; poso 162
(define poso (lambda (n) (fresh (h  t ) (== n (h + t)) )
; appendo 162
(define appendo (lambda (l, s, out)
                (conde ((== l '())
                      (== s out))
                      ((fresh (a d res)
                         (== (a + d) l)
                         (== (a + res) out)
                         (appendo d s res)
                         )
                      )
                 )
; gt1o 162
(define gt1o (lambda (n)
             (fresh (a  ad  dd ) (== n (a + (ad + dd))) )
