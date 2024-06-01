; FUCK

;;; There are 4 relations
; zeroo 143
(define zeroo (lambda (n)
                                                n `===` nilLogicList())
; poso 143
(define poso (lambda (n)
             freshTypedVars { h: Term<LogicInt> t: Term<LogicList<LogicInt>> ->
             (n `===` (h + t)) })
; appendo 143
(define appendo (lambda (l, s, out)
                conde(and(l `===` nilLogicList(), s `===` out),
                      freshTypedVars { a: Term<LogicInt> d: Term<LogicList<LogicInt>> 
                        res: Term<LogicList<LogicInt>> ->
                      and((a + d) `===` l,
                          (a + res) `===` out,
                          appendo(d s res))
                      }))
; gt1o 143
(define gt1o (lambda (n)
             freshTypedVars { a: Term<LogicInt> ad: Term<LogicInt> dd: Term<LogicList<LogicInt>> ->
             (n `===` (a + (ad + dd))) })
