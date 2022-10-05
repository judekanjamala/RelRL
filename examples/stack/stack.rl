interface CELL =
  class Cell { cell_value: int; cell_rep: rgn; }
  meth Cell(self:Cell, k:int) : unit
    ensures { self.cell_value = k }
    ensures { self.cell_rep = {self} }
    effects { rw {self}`any; rd self, k }
end

module Cell : CELL =
  class Cell { cell_value: int; cell_rep: rgn; }
  meth Cell(self:Cell, k:int) : unit
  = self.cell_value := k; self.cell_rep := {self};
end

interface STACK =
  import CELL
  import theory Stack_theory

  extern type intList with default = nil
  extern hd(intList) : int
  extern tl(intList) : intList
  extern cons(int,intList) : intList
  extern listNth(int,intList) : int
  extern listLength(intList) : int

  /* TODO: rename size to numElements, maxSize to capacity? */
  class Stack { rep: rgn; size: int; ghost contents: intList; }
  
  ghost pool : rgn
  public maxSize : int

  boundary { maxSize, pool, pool`any, pool`rep`any }
  
  public invariant stackPub =
    maxSize > 0 /\
    Type(pool, Stack | Cell) /\
    (forall s:Stack in pool.
      let sz = s.size in let xs = s.contents in 
      sz = listLength(xs) /\ 0 <= sz /\ sz <= maxSize) /\
    (forall s:Stack in pool, t: Stack in pool.
      let srep = s.rep in
      let trep = t.rep in
      s <> t -> srep # trep)

  /* meth getMaxSize () : int ensures { result = maxSize } effects { rd maxSize } */

  meth Stack(self:Stack) : unit
    requires { ~(self in pool) }
    ensures  { self.size = 0 }
    ensures  { self.contents = nil }
    ensures  { let opool = old(pool) in pool = opool union {self} }
    effects  { rw {self}`any /*, {self}`rep`any */, alloc, pool; rd self, maxSize }

  meth isEmpty(self:Stack) : bool
    requires { self in pool }
    ensures  { result <-> self.size = 0 }
    effects  { rd self, {self}`any }

  /* TODO: consider version with k:Cell as parameter */
  meth push(self:Stack, k:int) : unit
    requires { self in pool }
    requires { let sz = self.size in sz < maxSize }
    ensures  { let osz = old(self.size) in self.size = osz + 1 }
    ensures  { let xs = old(self.contents) in self.contents = cons(k,xs) }
    effects  { rw {self}`any, {self}`rep`any, alloc; rd self, k, maxSize }

  meth pop(self:Stack) : Cell
    requires { self in pool }
    requires { let sz = self.size in sz > 0 }
    ensures  { let osz = old(self.size) in self.size = osz - 1 }
    ensures  { let oxs = old(self.contents) in
               let t = hd(oxs) in
	       result.cell_value = t }
    ensures  { let ostk = old(self.contents) in self.contents = tl(ostk) }
    effects  { rw {self}`any, {self}`rep`any, alloc, result, {result}`any; rd self, maxSize }

end
