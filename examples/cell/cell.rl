interface CELL =

  class Cell { value: int; rep: rgn; }

  ghost pool : rgn

  boundary  { pool, pool`any, pool`rep`any }

  predicate cellP (r:rgn) [%public] = forall c:Cell in r, d:Cell in r.
    let crep = c.rep in
    let drep = d.rep in
    c <> d -> crep # drep

  meth Cell (self:Cell+, k:int) : unit
    requires { ~(self in pool) }
    requires { self.rep = {} }
    requires { cellP (pool) }
    requires { k >= 0 }
    ensures  { cellP (pool) }
    ensures  { self in pool }
    effects  { rw {self}`any, alloc, pool; rd k }

  meth cset (self:Cell+, k:int) : unit
    requires { self in pool }
    requires { cellP (pool) }
    requires { k >= 0 }
    ensures  { cellP (pool) }
    effects  { rw {self}`any, alloc; rd k }

  meth cget (self:Cell+) : int
    requires { self in pool }
    requires { cellP (pool) }
    ensures  { cellP (pool) }
    ensures  { result >= 0 }
    effects  { rd {self}`any; rw alloc }

end

module ACell : CELL =

  class Cell { value: int; rep: rgn; }

  predicate cellI (r:rgn) [%private] = forall c:Cell in r.
    c.rep = {c} /\ let v = c.value in v >= 0

  meth Cell (self:Cell+, k:int) : unit
    requires { cellI (pool) } ensures { cellI (pool) }
  = self.value := k;
    self.rep := {self};
    pool := pool union {self};

  meth cset (self:Cell+, k:int) : unit
    requires { cellI (pool) } ensures { cellI (pool) }
  = self.value := k;

  meth cget (self:Cell+) : int
    requires { cellI (pool) } ensures { cellI (pool) }
  = result := self.value;

end

module BCell : CELL =

  class Cell
  { value : int;
    rep   : rgn;
  }

  predicate cellI (r:rgn) [%private] = forall c:Cell in r.
    let v = c.value in
    v <= 0 /\ c.rep = {c}

  meth Cell (self:Cell+, k:int) : unit
    requires { cellI (pool) } ensures { cellI (pool) }
  = if k <= 0 then
      self.value := k;
    else
      self.value := -k;
    end;
    self.rep := {self};
    pool := pool union {self};


  meth cset (self:Cell+, k:int) : unit
    requires { cellI (pool) } ensures { cellI (pool) }
  = if k <= 0 then
      self.value := k;
    else
      self.value := -k;
    end;

  meth cget (self:Cell+) : int
    requires { cellI (pool) } ensures { cellI (pool) }
  = var value : int in
    value := self.value;
    result := -value;

end

bimodule CELL_REL ( ACell | BCell ) =

  predicate coupling (pl:rgn | pl:rgn) =
    forall c:Cell in pl | c:Cell in pl.
      Both (cellI (pl)) /\ (c =:= c -> let v|v = c.value|c.value in v =:= -v)

  meth Cell (self:Cell+,k:int | self:Cell+,k:int) : (unit | unit)
    requires { coupling(pool | pool) }
    ensures  { coupling(pool | pool) }
    requires { Both (~(self in pool)) }
    requires { Both (self.rep = {}) }
    requires { Both (cellP(pool)) }
    requires { Both (cellI(pool)) }
    requires { let rp|rp = self.rep|self.rep in rp =:= rp }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    requires { k =:= k }
    requires { self =:= self }
    requires { Both (k >= 0) }
    ensures  { Both (cellP(pool)) }
    ensures  { Both (cellI(pool)) }
    ensures  { Both (self in pool) }
    effects  { rw {self}`any, alloc, pool; rd k
             | rw {self}`any, alloc, pool; rd k }
  = ( self.value := k
    | if k <= 0 then self.value := k else self.value := -k end; );
    Assert { Both (k >= 0) -> let v|v = self.value|self.value in v =:= -v };
    |_ self.rep := {self} _|;
    |_ pool := pool union {self} _|;

  meth cset (self:Cell+,k:int | self:Cell+,k:int) : (unit | unit)
    requires { coupling(pool | pool) }
    ensures  { coupling(pool | pool) }
    requires { Both (self in pool) }
    requires { Both (cellP(pool)) }
    requires { Both (cellI(pool)) }
    requires { let rep|rep = self.rep|self.rep in rep =:= rep }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    requires { k =:= k }
    requires { Both (k >= 0) }
    ensures  { let rep|rep = self.rep|self.rep in rep =:= rep }
    ensures  { Both (cellP(pool)) }
    ensures  { Both (cellI(pool)) }
    effects  { rw {self}`any, alloc, pool; rd k
             | rw {self}`any, alloc, pool; rd k }
  = Assert { self =:= self };
    ( self.value := k
    | if k <= 0 then self.value := k else self.value := -k end; );

  meth cget (self:Cell+ | self:Cell+) : (int | int)
    requires { coupling(pool | pool) }
    ensures  { coupling(pool | pool) }
    requires { Both (self in pool) }
    requires { Both (cellP(pool)) }
    requires { Both (cellI(pool)) }
    requires { let rep|rep = self.rep|self.rep in rep =:= rep }
    requires { let vl|vl = self.value|self.value in vl =:= -vl }
    ensures  { Both (cellP(pool)) }
    ensures  { Both (cellI(pool)) }
    ensures  { Both (result >= 0) }
    ensures  { result =:= result }
    effects  { rw {self}`any, alloc, pool
             | rw {self}`any, alloc, pool }
  = ( result := self.value
    | var value : int in
      value := self.value;
      result := -value );

end

interface CLIENT = end

module Client : CLIENT =

  import CELL

  meth main (x:int) : int
    requires { pool = {} }
    requires { x >= 0 }
    effects { rw alloc, pool, x }
  = var c : Cell in
    c := new Cell;
    var k : int in
    k := 0;
    Cell (c, k);
    { c in alloc };
    x := x + 1;
    cset (c, x);
    result := cget (c);

end

bimodule CLIENT_REL (Client | Client) =

  import CELL_REL

  meth main (x:int | x:int) : (int | int)
    requires { Both (pool = {}) }
    requires { Both (x >= 0) }
    requires { x =:= x }
    ensures  { result =:= result }
    effects  { rw alloc, pool, x
             | rw alloc, pool, x }
  = Var c : Cell | c : Cell in
    |_ c := new Cell _|;
    Link c with c; {{ c =:= c }};
    Assert { Both (let rep = c.rep in rep = {}) };
    Var k : int | k : int in
    |_ k := 0 _|;
    |_ Cell (c, k) _|;
    Assert { Both (c in alloc) };
    |_ x := x + 1 _|;
    |_ cset (c, x) _|;
    |_ result := cget (c) _|;

end
