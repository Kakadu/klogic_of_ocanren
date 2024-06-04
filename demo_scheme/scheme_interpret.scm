
;;; There are 4 relations
; lookupo 266
#|
(AST.Fresh (
                                               [("rest", ?); ("y", ?);
                                                 ("v", ?)],
                                               (AST.Pause
                                                  (AST.Conj_multi
                                                     [(AST.Unify (
                                                         (AST.T_list_cons (
                                                            (AST.Call_rel (
                                                               OCanren!.Std.Pair.pair,
                                                               [?; ?])),
                                                            ?)),
                                                         ?));
                                                       (AST.Conde
                                                          [(AST.Infix_conj2 (
                                                              (AST.Unify (?,
                                                                 ?)),
                                                              (AST.Unify (?,
                                                                 ?))
                                                              ));
                                                            (AST.Infix_conj2 (
                                                               (AST.Diseq (?,
                                                                  ?)),
                                                               (AST.Call_rel (
                                                                  lookupo/1408,
                                                                  [?; ?; ?]))
                                                               ))
                                                            ])
                                                       ]))
                                               ))
|#
(define lookupo
  (lambda (x env t)
  (fresh (rest y v)
    (== `((,y ,v) . ,rest) env)
    (conde ((== y x)
          (== v t))
          ((=/= y x)
          (lookupo x rest t))
          )
     
    )))
; not_in_envo 266
#|
(AST.Conde
                        [(AST.Fresh ([("y", ?); ("v", ?); ("rest", ?)],
                            (AST.Pause
                               (AST.Conj_multi
                                  [(AST.Unify (?,
                                      (AST.T_list_cons (
                                         (AST.Call_rel (OCanren!.Std.pair,
                                            [?; ?])),
                                         ?))
                                      ));
                                    (AST.Diseq (?, ?));
                                    (AST.Call_rel (not_in_envo/1769, [?; ?]))
                                    ]))
                            ));
                          (AST.Unify (AST.T_list_nil, ?))])
|#
(define not_in_envo
  (lambda (x env)
  (conde ((fresh (y v rest)
            (== env `((,y ,v) . ,rest))
            (=/= y x)
            (not_in_envo x rest)
            ))
        ((== '() env))
        )
   ))
; proper_listo 266
#|
(AST.Conde
                         [(AST.Infix_conj2 ((AST.Unify (AST.T_list_nil, ?)),
                             (AST.Unify (AST.T_list_nil, ?))));
                           (AST.Fresh (
                              [("e", ?); ("d", ?); ("te", ?); ("td", ?)],
                              (AST.Pause
                                 (AST.Conj_multi
                                    [(AST.Unify (?, (AST.T_list_cons (?, ?))
                                        ));
                                      (AST.Unify (?, (AST.T_list_cons (?, ?))
                                         ));
                                      (AST.Call_rel (evalo/1777,
                                         [?; ?;
                                           (AST.Call_rel (
                                              Scheme_ast!.Gresult.val_, 
                                              [?]))
                                           ]
                                         ));
                                      (AST.Call_rel (proper_listo/1776,
                                         [?; ?; ?]))
                                      ]))
                              ))
                           ])
|#
(define proper_listo
  (lambda (es env rs)
  (conde ((== '() es)
        (== '() rs))
        ((fresh (e d te td)
           (== es `(,e . ,d))
           (== rs `(,te . ,td))
           (evalo e env `(val ,te))
           (proper_listo d env td)
           ))
        )
   ))
; evalo 266
#|
(AST.Conde
                  [(AST.Fresh ([("t", ?)],
                      (AST.Pause
                         (AST.Conj_multi
                            [(AST.Unify (?,
                                (AST.Call_rel (Scheme_ast!.Gterm.seq,
                                   [(AST.T_list_cons (
                                       (AST.Call_rel (Scheme_ast!.Gterm.symb,
                                          [(AST.T_string "quote")])),
                                       (AST.T_list_cons (?, AST.T_list_nil))
                                       ))
                                     ]
                                   ))
                                ));
                              (AST.Unify (?,
                                 (AST.Call_rel (Scheme_ast!.Gresult.val_, 
                                    [?]))
                                 ));
                              (AST.Call_rel (not_in_envo/1769,
                                 [(AST.T_string "quote"); ?]))
                              ]))
                      ));
                    (AST.Fresh ([("es", ?); ("rs", ?)],
                       (AST.Pause
                          (AST.Conj_multi
                             [(AST.Unify (?,
                                 (AST.Call_rel (Scheme_ast!.Gterm.seq,
                                    [(AST.T_list_cons (
                                        (AST.Call_rel (
                                           Scheme_ast!.Gterm.symb,
                                           [(AST.T_string "list")])),
                                        ?))
                                      ]
                                    ))
                                 ));
                               (AST.Unify (?,
                                  (AST.Call_rel (Scheme_ast!.Gresult.val_,
                                     [(AST.Call_rel (Scheme_ast!.Gterm.seq,
                                         [?]))
                                       ]
                                     ))
                                  ));
                               (AST.Call_rel (not_in_envo/1769,
                                  [(AST.T_string "list"); ?]));
                               (AST.Call_rel (proper_listo/1776, [?; ?; ?]))]))
                       ));
                    (AST.Fresh ([("s", ?)],
                       (AST.Pause
                          (AST.Conj_multi
                             [(AST.Unify (?,
                                 (AST.Call_rel (Scheme_ast!.Gterm.symb, [?]))
                                 ));
                               (AST.Call_rel (lookupo/1408, [?; ?; ?]))]))
                       ));
                    (AST.Fresh (
                       [("func", ?); ("arge", ?); ("arg", ?); ("x", ?);
                         ("body", ?)],
                       (AST.Fresh ([("env2", ?)],
                          (AST.Pause
                             (AST.Conj_multi
                                [(AST.Unify (?,
                                    (AST.Call_rel (Scheme_ast!.Gterm.seq,
                                       [(AST.T_list_cons (?,
                                           (AST.T_list_cons (?,
                                              AST.T_list_nil))
                                           ))
                                         ]
                                       ))
                                    ));
                                  (AST.Call_rel (evalo/1777, [?; ?; ?]));
                                  (AST.Call_rel (evalo/1777,
                                     [?; ?;
                                       (AST.Call_rel (
                                          Scheme_ast!.Gresult.closure,
                                          [?; ?; ?]))
                                       ]
                                     ));
                                  (AST.Call_rel (evalo/1777,
                                     [?;
                                       (AST.T_list_cons (
                                          (AST.Call_rel (OCanren!.Std.pair,
                                             [?; ?])),
                                          ?));
                                       ?]
                                     ))
                                  ]))
                          ))
                       ));
                    (AST.Fresh ([("x", ?); ("body", ?)],
                       (AST.Pause
                          (AST.Conj_multi
                             [(AST.Unify (?,
                                 (AST.Call_rel (Scheme_ast!.Gterm.seq,
                                    [(AST.T_list_cons (
                                        (AST.Call_rel (
                                           Scheme_ast!.Gterm.symb,
                                           [(AST.T_string "lambda")])),
                                        (AST.T_list_cons (
                                           (AST.Call_rel (
                                              Scheme_ast!.Gterm.seq,
                                              [(AST.T_list_cons (
                                                  (AST.Call_rel (
                                                     Scheme_ast!.Gterm.symb,
                                                     [?])),
                                                  AST.T_list_nil))
                                                ]
                                              )),
                                           (AST.T_list_cons (?,
                                              AST.T_list_nil))
                                           ))
                                        ))
                                      ]
                                    ))
                                 ));
                               (AST.Call_rel (not_in_envo/1769,
                                  [(AST.T_string "lambda"); ?]));
                               (AST.Unify (?,
                                  (AST.Call_rel (Scheme_ast!.Gresult.closure,
                                     [?; ?; ?]))
                                  ))
                               ]))
                       ))
                    ])
|#
(define evalo
  (lambda (term env r)
  (conde ((fresh (t)
            (== term `(seq ((symb 'quote),t)))
            (== r `(val ,t))
            (not_in_envo 'quote env)
            ))
        ((fresh (es rs)
           (== term `(seq ((symb 'list) . ,es)))
           (== r `(val (seq ,rs)))
           (not_in_envo 'list env)
           (proper_listo es env rs)
           ))
        ((fresh (s)
           (== term `(symb ,s))
           (lookupo s env r)
           ))
        ((fresh ( func   arge   arg   x   body )
         (fresh (env2)
           (== term `(seq (,func,arge)))
           (evalo arge env arg)
           (evalo func env `(closure ,x ,body ,env2))
           (evalo body `((,x ,arg) . ,env2) r)
           ) ))
        ((fresh (x body)
           (== term `(seq ((symb 'lambda)(seq ((symb ,x))),body)))
           (not_in_envo 'lambda env)
           (== r `(closure ,x ,body ,env))
           ))
        )
   ))

