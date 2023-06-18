// There are 3 realtions
fun poso(n: int OCanren.ilogic OCanren.Std.List.injected) =
  { st -> pause { fresh { h, t ->
                    (n/1 `===` (h + t))(st)} } }
fun zeroo(n: int OCanren.ilogic OCanren.Std.List.injected) =
  (logicListOf() `===` n/2)
fun appendo(l: int OCanren.ilogic OCanren.Std.List.injected,s: int OCanren.ilogic OCanren.Std.List.injected,out: int OCanren.ilogic OCanren.Std.List.injected) =
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
