; extraction from test-quines

(defrel (not-in-envo x env)
  (conde
    ((fresh (y v rest)
       (== `((,y . ,v) . ,rest) env)
       (=/= y x)
       (not-in-envo x rest)))
    ((== '() env))))

(defrel (proper-listo exp env val)
  (conde
    ((== '() exp)
     (== '() val))
    ((fresh (a d t-a t-d)
       (== `(,a . ,d) exp)
       (== `(,t-a . ,t-d) val)
       (eval-expo a env t-a)
       (proper-listo d env t-d)))))

(defrel (lookupo x env t)
  (fresh (rest y v)
    (== `((,y . ,v) . ,rest) env)
    (conde
      ((== y x) (== v t))
      ((=/= y x) (lookupo x rest t)))))

(defrel (eval-expo exp env val)
  (conde
    ((fresh (v)
       (== `(quote ,v) exp)
       (== v val)
       (not-in-envo 'quote env)
       (absento 'closure v)))
    ((fresh (a*)
       (== exp `(list . ,a*) )
       (not-in-envo 'list env)
       (absento 'closure a*)
       (proper-listo a* env val)))
    ((symbolo exp) (lookupo exp env val))
    ((fresh (rator rand arg x body)
     (fresh (env^)
       (== `(,rator ,rand) exp)
       (eval-expo rand env arg)
       (eval-expo rator env `(closure ,x ,body ,env^))
       (eval-expo body `((,x . ,arg) . ,env^) val))))
    ((fresh (x body)
       (== `(lambda (,x) ,body) exp)
       (symbolo x)
       (not-in-envo 'lambda env)
       (== `(closure ,x ,body ,env) val)))))

