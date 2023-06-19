// Put imports here
// Multilines are supported

// There are 8 relations
fun poso(n: Term<LogicList<LogicInt>>) =
  { st -> pause { fresh { h, t ->
                    (n `===` (h + t))(st)} } }
fun zeroo(n: Term<LogicList<LogicInt>>) =
  (logicListOf() `===` n)
fun appendo(l: Term<LogicList<LogicInt>>, s: Term<LogicList<LogicInt>>,
out: Term<LogicList<LogicInt>>) =
  { st ->
  pause { mplus(
            bind(
              (l `===` logicListOf())(st),
              (s `===` out)
              ),
            pause { { st ->
                    pause { fresh { a, d, res ->
                              bind(
                                bind(
                                  ((a + d) `===` l)(st),
                                  ((a + res) `===` out)
                                  ),
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
                    (0 `===` b)(st),
                    (0 `===` x)
                    ),
                  (0 `===` y)
                  ),
                (0 `===` r)
                ),
              (0 `===` c)
              ),
            pause { mplus(
                      bind(
                        bind(
                          bind(
                            bind(
                              (1 `===` b)(st),
                              (0 `===` x)
                              ),
                            (0 `===` y)
                            ),
                          (1 `===` r)
                          ),
                        (0 `===` c)
                        ),
                      pause { mplus(
                                bind(
                                  bind(
                                    bind(
                                      bind(
                                        (0 `===` b)(st),
                                        (1 `===` x)
                                        ),
                                      (0 `===` y)
                                      ),
                                    (1 `===` r)
                                    ),
                                  (0 `===` c)
                                  ),
                                pause { mplus(
                                          bind(
                                            bind(
                                              bind(
                                                bind(
                                                  (1 `===` b)(st),
                                                  (1 `===` x)
                                                  ),
                                                (0 `===` y)
                                                ),
                                              (0 `===` r)
                                              ),
                                            (1 `===` c)
                                            ),
                                          pause { mplus(
                                                    bind(
                                                      bind(
                                                        bind(
                                                          bind(
                                                            (0 `===` b)(st),
                                                            (0 `===` x)
                                                            ),
                                                          (1 `===` y)
                                                          ),
                                                        (1 `===` r)
                                                        ),
                                                      (0 `===` c)
                                                      ),
                                                    pause { mplus(
                                                              bind(
                                                                bind(
                                                                  bind(
                                                                    bind(
                                                                    (1 `===` b)(st),
                                                                    (0 `===` x)
                                                                    ),
                                                                    (1 `===` y)
                                                                    ),
                                                                  (0 `===` r)
                                                                  ),
                                                                (1 `===` c)
                                                                ),
                                                              pause { 
                                                              mplus(
                                                                bind(
                                                                  bind(
                                                                    bind(
                                                                    bind(
                                                                    (0 `===` b)(st),
                                                                    (1 `===` x)
                                                                    ),
                                                                    (1 `===` y)
                                                                    ),
                                                                    (0 `===` r)
                                                                    ),
                                                                  (1 `===` c)
                                                                  ),
                                                                pause { 
                                                                bind(
                                                                  bind(
                                                                    bind(
                                                                    bind(
                                                                    (1 `===` b)(st),
                                                                    (1 `===` x)
                                                                    ),
                                                                    (1 `===` y)
                                                                    ),
                                                                    (1 `===` r)
                                                                    ),
                                                                  (1 `===` c)
                                                                  )
                                                                })
                                                              })
                                                    })
                                          })
                                })
                      })
            })
  } }
fun addero(d: Term<LogicInt>, n: Term<LogicList<LogicInt>>,
m: Term<LogicList<LogicInt>>, r: Term<LogicList<LogicInt>>) =
  { st ->
  pause { mplus(
            bind(
              bind(
                (0 `===` d)(st),
                (logicListOf() `===` m)
                ),
              (n `===` r)
              ),
            pause { mplus(
                      bind(
                        bind(
                          bind(
                            (0 `===` d)(st),
                            (logicListOf() `===` n)
                            ),
                          (m `===` r)
                          ),
                        poso(m)
                        ),
                      pause { mplus(
                                bind(
                                  bind(
                                    (1 `===` d)(st),
                                    (logicListOf() `===` m)
                                    ),
                                  addero(0,n,one,r)
                                  ),
                                pause { mplus(
                                          bind(
                                            bind(
                                              bind(
                                                (1 `===` d)(st),
                                                (logicListOf() `===` n)
                                                ),
                                              poso(m)
                                              ),
                                            addero(0,m,one,r)
                                            ),
                                          pause { mplus(
                                                    bind(
                                                      bind(
                                                        (n `===` one)(st),
                                                        (m `===` one)
                                                        ),
                                                      { st ->
                                                      pause { fresh { a, c ->
                                                                bind(
                                                                  (OCanren.Std.%<(a,c) `===` r)(st),
                                                                  full_addero(d,1,1,a,c)
                                                                  )}
                                                      } } ),
                                                    pause { mplus(
                                                              bind(
                                                                (n `===` one)(st),
                                                                gen_addero(d,n,m,r)
                                                                ),
                                                              pause { 
                                                              mplus(
                                                                bind(
                                                                  bind(
                                                                    bind(
                                                                    (m `===` one)(st),
                                                                    gt1o(n)
                                                                    ),
                                                                    gt1o(r)
                                                                    ),
                                                                  addero(d,one,n,r)
                                                                  ),
                                                                pause { 
                                                                bind(
                                                                  gt1o(n)(st),
                                                                  gen_addero(d,n,m,r)
                                                                  )
                                                                })
                                                              })
                                                    })
                                                    })
                                          })
                                })
                      })
            }
  }
fun gen_addero(d: Term<LogicInt>, n: Term<LogicList<LogicInt>>,
m: Term<LogicList<LogicInt>>, r: Term<LogicList<LogicInt>>) =
  { st ->
  pause { fresh { a, b, c, e, x, y, z ->
            bind(
              bind(
                bind(
                  bind(
                    bind(
                      bind(
                        ((a + x) `===` n)(st),
                        ((b + y) `===` m)
                        ),
                      poso(y)
                      ),
                    ((c + z) `===` r)
                    ),
                  poso(z)
                  ),
                full_addero(d,a,b,c,e)
                ),
              addero(e,x,y,z)
              )}
  } }
fun pluso(n: Term<LogicList<LogicInt>>, m: Term<LogicList<LogicInt>>,
k: Term<LogicList<LogicInt>>) =
  addero(0,n,m,k)
fun minuso(n: Term<LogicList<LogicInt>>, m: Term<LogicList<LogicInt>>,
k: Term<LogicList<LogicInt>>) =
  pluso(m,k,n)
