  $ ./relationalClosureTests.exe
  Class A: 4
  Class B extends A: 5
  Class C extends B: 6
  Class A1: 7
  B <-1-< A: 
  [
    [Class (4, []); Class (5, [])]
  ]
  
  C <-1-< A: 
  [
    
  ]
  
  C <-2-< A: 
  [
    [Class (4, []); Class (5, []); Class (6, [])]
  ]
  
  C <-3-< A: 
  [
    [Class (4, []); Class (5, []); Var {id=_.62811, index=_.62812, upb=Class (5, []), lwb=Some (Class (6, []))}; Class (6, [])]
  ]
  
  Class Int: 4
  Interface ICollection: 5
  Class List: 7
  
  class  extends class 1
  interface <Var { id=6; index=0; upb=class 1 }>
  class <Var { id=8; index=0; upb=class 1 }> extends class 1 implements (interface 5<Var { id=8; index=0; upb=class 1 }>)
  ? <-< ICollection<int>: 
  [
    Class (7, [Type (Class (4, []))])
  ]
  
