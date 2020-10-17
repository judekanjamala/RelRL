interface LISTPUB =

  import theory Listpub_theory

  extern type intList with default = nil
  extern hd (intList) : int
  extern tl (intList) : intList
  extern sumList (intList) : int

  class Node { value : int; pub : bool; nxt : Node; }

  class List { head : Node; rep : rgn; }

  predicate rep_closed (xs:List) =
    xs <> null ->
    let hd = xs.head in
    let rep = xs.rep in
    Type(rep,Node) /\ rep`nxt subset rep /\ null in rep /\ hd in rep

  lemma rep_closed_prop : forall xs:List.
    rep_closed(xs) ->
    let rep = xs.rep in
    forall n:Node in rep.
      let nxt = n.nxt in
      nxt in rep

  predicate sim (n:Node, l:intList) = false
/* NOTE: sim is replaced by post-process.py
  
   If sim could be expressed in our source language:

   inductive sim : Node -> intList -> prop =
   | sim_nil : sim null nil
   | sim_del : n.pub = false -> sim n.nxt l -> sim n l
   | sim_pub : n.pub = true  -> sim n.nxt l -> sim n (cons n.value l)
*/

   predicate simL (xs:List, ls:intList) =
    xs <> null ->
    let hd = xs.head in
    sim(hd, ls)

  lemma sim_nxt : forall n:Node,xs:intList.
    sim(n,xs) ->
    let nxt = n.nxt in
    exists xs':intList. sim(nxt,xs')

  lemma sim_unique : forall xs:intList,n:Node.
    sim(n,xs) -> forall ys:intList. sim (n,ys) -> xs = ys

  lemma sim_nexists : forall n:Node.
    n.nxt = n ->
    ~ (exists ls:intList. sim(n,ls))

  meth sum (self:List+) : int
    requires { exists l:intList. simL(self,l) }
    requires { rep_closed (self) }
    ensures  { rep_closed (self) }
    ensures  { exists l:intList. simL(self,l) /\ result = sumList(l) }
    reads { alloc, {self}`any, {self}`rep`any }

end


module ListPub : LISTPUB =

  class Node { value : int; pub : bool; nxt : Node; }

  class List { head : Node; rep : rgn; }

  meth sum (self:List+) : int
  = var ghost wit : intList in
    var ghost seg : intList in
    assume { simL(self,wit) };
    seg := wit;

    var p : Node in
    p := self.head;
    result := 0;

    while (p <> null) do
      invariant { let rep = self.rep in p in rep }
      invariant { sim(p,seg) }
      invariant { let sum = sumList(wit) in
                  let cur = sumList(seg) in
                  result = sum - cur }

      var pub : bool in
      pub := p.pub;

      if pub then
        var v:int in
        v := p.value;
        result := result + v;
        seg := tl(seg);
      end;

      p := p.nxt;
    done;

end

bimodule BiList (ListPub | ListPub) =

  import theory Listpub_theory

  /* NOTE experimental syntax: "{ p }" is parsed as "assert { p }". */

  meth sum (self:List+ | self:List+) : (int | int)
    requires { Both (exists l:intList. simL(self,l)) }
    requires { Both (rep_closed(self)) }
    requires { exists l:intList | l:intList. Both (simL(self,l)) /\ l =:= l }
    ensures  { Both (rep_closed(self)) }
    ensures  { Both (exists l:intList. simL(self,l)) }
    ensures  { result =:= result }
    effects  { rd alloc, {self}`any, {self}`rep`any
             | rd alloc, {self}`any, {self}`rep`any }
  = Var ghost wit : intList | ghost wit : intList in
    Var ghost seg : intList | ghost seg : intList in
    Assume { Both (simL(self,wit)) };
    |_ seg := wit _|;
    Var p : Node | p : Node in
    |_ p := self.head _|;
    |_ result := 0 _|;
    While (p <> null) | (p <> null) . <| p.pub = false <] | [> p.pub = false |> do
      invariant { Both (let rep = self.rep in p in rep) }
      invariant { Both (sim(p,seg)) }
      invariant { result =:= result }
      invariant { seg =:= seg }

      Var pub : bool | pub : bool in
      |_ pub := p.pub _|;

      ( if pub then
          var v : int in
          v := p.value; { v = hd(seg) };
          result := result + v;
          seg := tl(seg);
        end;
        p := p.nxt

      | if pub then
          var v : int in
          v := p.value; { v = hd(seg) };
          result := result + v;
          seg := tl(seg);
        end;
        p := p.nxt );
    done;

  meth sum2 (self:List+ | self:List+) : (int | int)
    requires { Both (exists l:intList. simL(self,l)) }
    requires { Both (rep_closed(self)) }
    requires { exists l:intList | l:intList. Both (simL(self,l)) /\ l =:= l }
    ensures  { Both (rep_closed(self)) }
    ensures  { Both (exists l:intList. simL(self,l)) }
    ensures  { result =:= result }
    effects  { rd alloc, {self}`any, {self}`rep`any
             | rd alloc, {self}`any, {self}`rep`any }
  = Var ghost wit : intList | ghost wit : intList in 
    Var ghost seg : intList | ghost seg : intList in 
    Assume { Both (simL(self,wit)) };
    |_ seg := wit _|;
    Var p : Node | p : Node in 
    |_ p := self.head _|;
    |_ result := 0 _|;
    While (p <> null) | (p <> null) .
        <| p.pub = false <] /\ [> p <> null -> p.pub = true |>
      | [> p.pub = false |> /\ <| p <> null -> p.pub = true <] do
      invariant { Both (let rep = self.rep in p in rep) }
      invariant { Both (sim(p,seg)) }
      invariant { result =:= result }
      invariant { seg =:= seg }

      Var pub : bool | pub : bool in 
      |_ pub := p.pub _|;

      ( if pub then
          var v : int in
          v := p.value; { v = hd(seg) };
          result := result + v;
          seg := tl (seg);
        end;
        p := p.nxt

      | if pub then
          var v : int in
          v := p.value; { v = hd(seg) };
          result := result + v;
          seg := tl (seg);
        end;
        p := p.nxt );
    done;

end
