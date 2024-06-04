
;;; There are 4 relations
; lookupo 234
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
                                                               (AST.Call_rel (
                                                                  =/=/1435,
                                                                  [?; ?])),
                                                               (AST.Call_rel (
                                                                  lookupo/1437,
                                                                  [?; ?; ?]))
                                                               ))
                                                            ])
                                                       ]))
                                               ))
|#
(define lookupo
  (lambda (x env t)
  (fresh (rest y v)
    (== `(,y ,v) . ,rest) env)
    (conde ((== y x)
          (== v t))
          ((equal_slash_equal y x)
          (lookupo x rest t))
          )
     
    )))
; not_in_envo 234
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
                                    (AST.Call_rel (=/=/1435, [?; ?]));
                                    (AST.Call_rel (not_in_envo/1798, [?; ?]))
                                    ]))
                            ));
                          (AST.Unify (AST.T_list_nil, ?))])
|#
(define not_in_envo
  (lambda (x env)
  (conde ((fresh (y v rest)
            (== env `(,y ,v) . ,rest))
            (equal_slash_equal y x)
            (not_in_envo x rest)
            ))
        ((== '() env))
        )
   ))
; proper_listo 234
#|
(AST.Conde
                         [(AST.Infix_conj2 (
                             (AST.Call_rel (====^/1432, [AST.T_list_nil; ?])),
                             (AST.Call_rel (====^/1432, [AST.T_list_nil; ?]))
                             ));
                           (AST.Fresh (
                              [("e", ?); ("d", ?); ("te", ?); ("td", ?)],
                              (AST.Pause
                                 (AST.Conj_multi
                                    [(AST.Call_rel (====^/1432,
                                        [?; (AST.T_list_cons (?, ?))]));
                                      (AST.Call_rel (====^/1432,
                                         [?; (AST.T_list_cons (?, ?))]));
                                      (AST.Call_rel (evalo/1806,
                                         [?; ?;
                                           (AST.Call_rel (
                                              Scheme_ast!.Gresult.val_, 
                                              [?]))
                                           ]
                                         ));
                                      (AST.Call_rel (proper_listo/1805,
                                         [?; ?; ?]))
                                      ]))
                              ))
                           ])
|#
(define proper_listo
  (lambda (es env rs)
  (conde ((equal_equal_equal_equal_hat '() es)
        (equal_equal_equal_equal_hat '() rs))
        ((fresh (e d te td)
           (equal_equal_equal_equal_hat es `(,e . ,d))
           (equal_equal_equal_equal_hat rs `(,te . ,td))
           (evalo e env (Scheme_ast.Gresult.val_ te))
           (proper_listo d env td)
           ))
        )
   ))
; evalo 234
#|
(AST.Conde
                  [(AST.Fresh ([("t", ?)],
                      (AST.Pause
                         (AST.Conj_multi
                            [(AST.Unify (?,
                                (AST.Call_rel (Scheme_ast!.Gterm.seq,
                                   [(AST.Call_rel (OCanren!.Std.%<,
                                       [(AST.Call_rel (
                                           Scheme_ast!.Gterm.symb,
                                           [(AST.T_string "quote")]));
                                         ?]
                                       ))
                                     ]
                                   ))
                                ));
                              (AST.Unify (?,
                                 (AST.Call_rel (Scheme_ast!.Gresult.val_, 
                                    [?]))
                                 ));
                              (AST.Call_rel (not_in_envo/1798,
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
                               (AST.Call_rel (not_in_envo/1798,
                                  [(AST.T_string "list"); ?]));
                               (AST.Call_rel (proper_listo/1805, [?; ?; ?]))]))
                       ));
                    (AST.Fresh ([("s", ?)],
                       (AST.Pause
                          (AST.Conj_multi
                             [(AST.Unify (?,
                                 (AST.Call_rel (Scheme_ast!.Gterm.symb, [?]))
                                 ));
                               (AST.Call_rel (lookupo/1437, [?; ?; ?]))]))
                       ));
                    (AST.Fresh (
                       [("func", ?); ("arge", ?); ("arg", ?); ("x", ?);
                         ("body", ?)],
                       (AST.Fresh ([("env'", ?)],
                          (AST.Pause
                             (AST.Conj_multi
                                [(AST.Unify (?,
                                    (AST.Call_rel (Scheme_ast!.Gterm.seq,
                                       [(AST.Call_rel (OCanren!.Std.%<,
                                           [?; ?]))
                                         ]
                                       ))
                                    ));
                                  (AST.Call_rel (evalo/1806, [?; ?; ?]));
                                  (AST.Call_rel (evalo/1806,
                                     [?; ?;
                                       (AST.Call_rel (
                                          Scheme_ast!.Gresult.closure,
                                          [?; ?; ?]))
                                       ]
                                     ));
                                  (AST.Call_rel (evalo/1806,
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
                                        (AST.Call_rel (OCanren!.Std.%<,
                                           [(AST.Call_rel (
                                               Scheme_ast!.Gterm.seq,
                                               [(AST.Call_rel (
                                                   OCanren!.Std.!<,
                                                   [(AST.Call_rel (
                                                       Scheme_ast!.Gterm.symb,
                                                       [?]))
                                                     ]
                                                   ))
                                                 ]
                                               ));
                                             ?]
                                           ))
                                        ))
                                      ]
                                    ))
                                 ));
                               (AST.Call_rel (not_in_envo/1798,
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
            (== term `#| (AST.Call_rel (Scheme_ast!.Gterm.seq,
                            [(AST.Call_rel (OCanren!.Std.%<,
                                [(AST.Call_rel (Scheme_ast!.Gterm.symb,
                                    [(AST.T_string "quote")]));
                                  ?]
                                ))
                              ]
                            )) |#)
            (== r `#| (AST.Call_rel (Scheme_ast!.Gresult.val_, [?])) |#)
            (not_in_envo 'quote env)
            ))
        ((fresh (es rs)
           (== term `#| (AST.Call_rel (Scheme_ast!.Gterm.seq,
                           [(AST.T_list_cons (
                               (AST.Call_rel (Scheme_ast!.Gterm.symb,
                                  [(AST.T_string "list")])),
                               ?))
                             ]
                           )) |#)
           (== r `#| (AST.Call_rel (Scheme_ast!.Gresult.val_,
                        [(AST.Call_rel (Scheme_ast!.Gterm.seq, [?]))])) |#)
           (not_in_envo 'list env)
           (proper_listo es env rs)
           ))
        ((fresh (s)
           (== term `('symb ,s))
           (lookupo s env r)
           ))
        ((fresh ( func   arge   arg   x   body )
         (fresh (env')
           (== term `#| (AST.Call_rel (Scheme_ast!.Gterm.seq,
                           [(AST.Call_rel (OCanren!.Std.%<, [?; ?]))])) |#)
           (evalo arge env arg)
           (evalo func env (Scheme_ast.Gresult.closure x body env_prime))
           (evalo body `(,x ,arg) . ,env_prime) r)
           ) ))
        ((fresh (x body)
           (== term `#| (AST.Call_rel (Scheme_ast!.Gterm.seq,
                           [(AST.T_list_cons (
                               (AST.Call_rel (Scheme_ast!.Gterm.symb,
                                  [(AST.T_string "lambda")])),
                               (AST.Call_rel (OCanren!.Std.%<,
                                  [(AST.Call_rel (Scheme_ast!.Gterm.seq,
                                      [(AST.Call_rel (OCanren!.Std.!<,
                                          [(AST.Call_rel (
                                              Scheme_ast!.Gterm.symb, 
                                              [?]))
                                            ]
                                          ))
                                        ]
                                      ));
                                    ?]
                                  ))
                               ))
                             ]
                           )) |#)
           (not_in_envo 'lambda env)
           (== r `#| (AST.Call_rel (Scheme_ast!.Gresult.closure, [?; ?; ?])) |#)
           ))
        )
   ))

