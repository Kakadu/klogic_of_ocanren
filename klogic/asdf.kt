// There are 4 realtions
fun poso(n: Term<LogicList<LogicInt>>) =
  { st -> pause { fresh { h, t ->
                    (n/1 `===` (h + t))(st)} } }
fun zeroo(n: Term<LogicList<LogicInt>>) =
  (logicListOf() `===` n/2)
fun appendo(l: Term<LogicList<LogicInt>>, s: Term<LogicList<LogicInt>>,
out: Term<LogicList<LogicInt>>) =
  { st ->
  pause { mplus(
            bind(
              (l `===` logicListOf())(st)
              (s `===` out)
              ),
            pause { { st ->
                    pause { fresh { a, d, res ->
                              bind(
                                bind(
                                  ((a + d) `===` l)(st)
                                  ((a + res) `===` out)
                                  )
                                appendo(d,s,res)
                                )}
                    } }(st)
                      })
            }
  }
fun full_addero(b: Term<LogicInt>, x: Term<LogicInt>, y: Term<LogicInt>,
r: Term<LogicInt>, c: Term<LogicInt>) =
  { st ->
  pause { mplus(
            bind(
              bind(
                bind(
                  bind(
                    (OCanren.!!({| 0 |}) `===` b)(st)
                    (OCanren.!!({| 0 |}) `===` x)
                    )
                  (OCanren.!!({| 0 |}) `===` y)
                  )
                (OCanren.!!({| 0 |}) `===` r)
                )
              (OCanren.!!({| 0 |}) `===` c)
              ),
            pause { OCanren.mplus(OCanren.bind(OCanren.bind(OCanren.bind(
                                                            OCanren.bind(
                                                            OCanren.===(
                                                            OCanren.!!({| 
                                                            1 |}),b)(st),
                                                            OCanren.===(
                                                            OCanren.!!({| 
                                                            0 |}),x)),
                                                            OCanren.===(
                                                            OCanren.!!({| 
                                                            0 |}),y)),
                                               OCanren.===(OCanren.!!({| 
                                                           1 |}),r)),
                                  OCanren.===(OCanren.!!({| 0 |}),c)),
                    OCanren.pause({| fun () ->
                                       mplus
                                         (bind
                                            (bind
                                               (bind
                                                  (bind (((!! 0) === b) st)
                                                     ((!! 1) === x))
                                                  ((!! 0) === y))
                                               ((!! 1) === r)) ((!! 0) === c))
                                         (pause
                                            (fun () ->
                                               mplus
                                                 (bind
                                                    (bind
                                                       (bind
                                                          (bind
                                                             (((!! 1) === b)
                                                                st)
                                                             ((!! 1) === x))
                                                          ((!! 0) === y))
                                                       ((!! 0) === r))
                                                    ((!! 1) === c))
                                                 (pause
                                                    (fun () ->
                                                       mplus
                                                         (bind
                                                            (bind
                                                               (bind
                                                                  (bind
                                                                    (((!! 0)
                                                                    === b) st)
                                                                    ((!! 0)
                                                                    === x))
                                                                  ((!! 1) ===
                                                                    y))
                                                               ((!! 1) === r))
                                                            ((!! 0) === c))
                                                         (pause
                                                            (fun () ->
                                                               mplus
                                                                 (bind
                                                                    (
                                                                    bind
                                                                    (bind
                                                                    (bind
                                                                    (((!! 1)
                                                                    === b) st)
                                                                    ((!! 0)
                                                                    === x))
                                                                    ((!! 1)
                                                                    === y))
                                                                    ((!! 0)
                                                                    === r))
                                                                    (
                                                                    (!! 1)
                                                                    === c))
                                                                 (pause
                                                                    (
                                                                    fun () ->
                                                                    mplus
                                                                    (bind
                                                                    (bind
                                                                    (bind
                                                                    (bind
                                                                    (((!! 0)
                                                                    === b) st)
                                                                    ((!! 1)
                                                                    === x))
                                                                    ((!! 1)
                                                                    === y))
                                                                    ((!! 0)
                                                                    === r))
                                                                    ((!! 1)
                                                                    === c))
                                                                    (pause
                                                                    (fun ()
                                                                    ->
                                                                    bind
                                                                    (bind
                                                                    (bind
                                                                    (bind
                                                                    (((!! 1)
                                                                    === b) st)
                                                                    ((!! 1)
                                                                    === x))
                                                                    ((!! 1)
                                                                    === y))
                                                                    ((!! 1)
                                                                    === r))
                                                                    ((!! 1)
                                                                    === c))))))))))) |}))
            })
  } }
