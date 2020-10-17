/* commuting method calls */

interface A =

  class K { a: int; b: int; }

  meth f (self:K+, k:int) : unit
    ensures { self.a = k }
    effects { wr {self}`a }

  meth g (self:K+, k:int) : unit
    ensures { self.b = k }
    effects { wr {self}`b }

  meth m (self:K+, k:int) : unit
    ensures { self.a = k /\ self.b = k }
    effects { wr {self}`any }

end

module A0 : A =

  class K { a: int; b: int; }

  meth f (self:K+, k:int) : unit =
    self.a := k;

  meth g (self:K+, k:int) : unit =
    self.b := k;

  meth m (self:K+, k:int) : unit =
    f (self, k);
    g (self, k);

end

module A1 : A =

  class K { a: int; b: int; }

  meth f (self:K+, k:int) : unit =
    self.a := k;

  meth g (self:K+, k:int) : unit =
    self.b := k;

  meth m (self:K+, k:int) : unit =
    g (self, k);
    f (self, k);

end

bimodule A_REL (A0 | A1) =

  meth f (self:K+, k:int | self:K+, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a }
    effects  { wr {self}`a | wr {self}`a }
  = |_ self.a := k _|;

  meth g (self:K+, k:int | self:K+, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`b }
    effects  { wr {self}`b | wr {self}`b }
  = |_ self.b := k _|;

  meth m (self:K+, k:int | self:K+, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { wr {self}`any | wr {self}`any }
  = ( f(self,k) | g(self,k) );
    ( g(self,k) | f(self,k) );

  meth m2 (self:K+, k:int | self:K+, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { wr {self}`any | wr {self}`any }
  = ( f(self,k); g(self,k) | g(self,k); f(self,k) );

end
