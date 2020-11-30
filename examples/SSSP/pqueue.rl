interface PQUEUE =

  class Node { tag: int; key: int; }

  class Pqueue { head: Node; size: int; rep: rgn; }

  ghost pool : rgn

  boundary { pool, pool`any, pool`rep`any }

  predicate pqueuePub () [%public] =
    Type(pool,Node|Pqueue) /\
    Type(pool`rep,Node) /\
    forall p:Pqueue in pool, q:Pqueue in pool.
      let prep = p.rep in
      let qrep = q.rep in
      p <> q -> prep # qrep

  meth Node (self:Node+, k:int, t:int) : unit
    ensures  { self.key = k }
    ensures  { self.tag = t }
    effects  { rw {self}`tag, {self}`key, alloc; rd k, t }

  meth getTag (self:Node+) : int
    ensures { result = self.tag }
    effects { rd self, {self}`tag }

  meth getKey (self:Node+) : int
    ensures { result = self.key }
    effects { rd self, {self}`key }

  meth Pqueue (self:Pqueue+) : unit
    requires { self.rep = {} /\ self.size = 0 /\ self.head = null }
    requires { pqueuePub () }
    requires { ~ (self in pool) }
    ensures  { self in pool }
    ensures  { pqueuePub () }
    ensures  { let rep = self.rep in rep subset {null} }
    effects  { rw pool, alloc; wr {self}`rep`any, {self}`any }

  meth isEmpty (self:Pqueue+) : bool
    requires { self in pool }
    requires { pqueuePub () }
    ensures  { self.size = 0 <-> result }
    ensures  { pqueuePub () }
    effects  { rd {self}`size }

  meth findMin (self:Pqueue+) : Node+
    requires { self in pool }
    requires { let sz = self.size in sz > 0 }
    requires { pqueuePub () }
    ensures  { pqueuePub () }
    ensures  { let hd = self.head in result = hd }
    effects  { rd {self}`head, alloc }

  meth insert (self:Pqueue+, k:int, t:int) : Node+
    requires { 0 <= k }
    requires { 0 <= t }
    requires { self in pool }
    requires { pqueuePub () }
    ensures  { pqueuePub () }
    ensures  { let rep = self.rep in result in rep }
    ensures  { let orep = old(self.rep) in self.rep = orep union {result} }
    ensures  { let osz = old(self.size) in self.size = osz + 1 }
    ensures  { result.key = k }
    ensures  { result.tag = t }
    ensures  { let rep = self.rep in forall n:Node in rep. n <> result -> 
                 let ot = old(n.tag) in
                 let ok = old(n.key) in
                 n.tag = ot /\ n.key = ok }
    effects  { rw {self}`head, {self}`size, {self}`rep, {self}`rep`any, alloc }

  meth deleteMin (self:Pqueue+) : Node+
    requires { self in pool }
    /* requires { let hd = self.head in hd <> null } */
    /* requires { let sz = self.size in sz > 0 } */
    requires { self.size <> 0 }
    requires { pqueuePub () }
    ensures  { let rep = self.rep in result in rep }
    ensures  { pqueuePub () }
    ensures  { let osz = old(self.size) in self.size = osz - 1 }
    ensures  { let orep = old(self.rep) in self.rep = orep }
    ensures  { let rep = self.rep in
               forall n:Node in rep.
                 let otag = old(n.tag) in
                 let okey = old(n.key) in
                 n.tag = otag /\ n.key = okey }
    effects  { rw {self}`any, {self}`rep`any, alloc }

  meth decreaseKey (self:Pqueue+, handle:Node+, k:int) : unit
    requires { self in pool }
    requires { let rep = self.rep in handle in rep }
    requires { 0 <= k }
    requires { let key = handle.key in k <= key }
    requires { let sz = self.size in sz > 0 }
    requires { pqueuePub () }
    ensures  { pqueuePub () }
    ensures  { handle.key = k }
    effects  { rw {self}`any, {self}`rep`any }

end

module PqueueL : PQUEUE =

  class Node { tag: int; key: int; prev: Node; sibling: Node; child: Node; }

  class NodeArray { length: int; slots: Node array; }

  class Pqueue { head: Node; size: int; rep: rgn; }

  predicate repClosed (rep:rgn) =
    Type(rep, Node) /\
    null in rep /\
    rep`sibling subset rep /\
    rep`child subset rep /\
    rep`prev subset rep

  lemma repClosed_DEF : forall r:rgn.
    repClosed(r) <->
    Type(r, Node) /\
    null in r /\
    forall n:Node in r.
      let sib = n.sibling in
      let pre = n.prev in
      let chl = n.child in
      sib in r /\ pre in r /\ chl in r

  predicate nodeP (r:rgn) = forall n:Node in r.
    let t = n.tag in
    let k = n.key in
    k >= 0 /\ t >= 0

  predicate strongDisjoint (r:rgn) = forall p:Pqueue in r, q:Pqueue in r.
    let prep = p.rep in
    let qrep = q.rep in
    p <> q -> prep inter qrep = {null}

  predicate pqueueI () [%private] = forall p:Pqueue in pool.
    let rep = p.rep in
    let sz = p.size in
    let hd = p.head in
    repClosed (rep) /\
    sz >= 0 /\
    hd in rep /\
    (sz = 0 <-> hd = null) /\
    nodeP (rep)
    /* strongDisjoint (pool) */

  lemma disjointNotIn : forall r:rgn.
    forall p:Pqueue in pool, q:Pqueue in pool.
      pqueuePub () ->
      p <> q ->
      let prep = p.rep in
      let qrep = q.rep in
      forall n:Node in prep. ~ (n in qrep)

  meth Node (self:Node+, k:int, t:int) : unit
    requires { self.sibling = null }
    requires { self.prev = null }
    requires { self.child = null }
    ensures  { self.sibling = null }
    ensures  { self.prev = null }
    ensures  { self.child = null }
  = self.key := k;
    self.tag := t;

  meth getTag (self:Node+) : int
  = result := self.tag;

  meth getKey (self:Node+) : int
  = result := self.key;

  meth Pqueue (self:Pqueue+) : unit
    requires { pqueueI () }
    ensures  { pqueueI () }
  = self.rep := {null};
    pool := pool union {self};

  meth isEmpty (self:Pqueue+) : bool
    requires { pqueueI () }
    ensures  { pqueueI () }
  = var sz : int in
    sz := self.size;
    result := sz = 0;

  meth findMin (self:Pqueue+) : Node+
    requires { pqueueI () }
    ensures  { pqueueI () }
  = { self.head <> null };
    result := self.head;

  meth link (self:Pqueue+, first:Node+, second:Node+) : Node+
    requires { self in pool }
    requires { let rep = self.rep in first in rep /\ second in rep }
    requires { pqueuePub () }
    requires { pqueueI () }
    ensures  { pqueuePub () }
    ensures  { pqueueI () }
    ensures  { (result = first /\ first.child = second) \/
               (result = second /\ second.child = first) }
    ensures  { result = first \/ result = second }
    /* ensures  { result = first -> first.child = second } */
    /* ensures  { result = second -> second.child = first } */
    ensures  { let rep = self.rep in result in rep }
    writes   { {self}`rep`child, {self}`rep`prev, {self}`rep`sibling }
    reads    { {self}`rep`any }
  = var fkey : int in
    var skey : int in
    var tmp : Node in
    var rep : rgn in
    rep := self.rep; fkey := first.key; skey := second.key;
    if skey < fkey then
        /* second.prev := first.prev */
        tmp := first.prev;
        { tmp in rep };
        second.prev := tmp;
        first.prev := second;
        { let p = first.prev in p in rep };
        /* first.sibling := second.child */
        tmp := second.child;
        first.sibling := tmp;
        /* first.sibling <> null */
        if tmp <> null then
            /* first.sibling.prev := first */
            tmp := first.sibling;
            tmp.prev := first;
            { tmp in rep };
            { let p = tmp.prev in p in rep };
            { repClosed (rep) };
        end;
        second.child := first;
        result := second;
        { repClosed (rep) };
    else
        second.prev := first;
        /* first.sibling := second.sibling */
        tmp := second.sibling;
        { tmp in rep };
        first.sibling := tmp;
        /* first.sibling <> null */
        if tmp <> null then
            /* first.sibling.prev := first */
            tmp := first.sibling;
            { tmp in rep };
            tmp.prev := first;
        end;
        /* second.sibling := first.child */
        tmp := first.child;
        second.sibling := tmp;
        /* second.sibling <> null */
        if tmp <> null then
            /* second.sibling.prev := second */
            tmp := second.sibling;
            { tmp in rep };
            tmp.prev := second;
        end;
        first.child := second;
        result := first;
        { repClosed (rep) };
    end;

  lemma insert_wr_rgn_eq : forall self:Pqueue, n:Node.
    let rep = self.rep in
    n in rep ->
    {n} union {self}`rep = {self}`rep

  lemma img_rep_lem : forall self:Pqueue. {self}`rep = self.rep

  meth insert (self:Pqueue+, k:int, t:int) : Node+
    requires { pqueueI () }
    ensures  { pqueueI () }
  = { pqueuePub () };
    result := new Node;  { pqueueI () }; { result <> null };
    Node (result, k, t);
    { pqueuePub () };
    { forall p:Pqueue in pool. let rep = p.rep in result notin rep };
    { pqueueI () };
    var rep : rgn in
    rep := self.rep;
    self.rep := rep union {result};

    { forall p:Pqueue in pool. p <> self ->
        let prep = p.rep in result notin prep };
    { forall p:Pqueue in pool. p <> self ->
        let prep = p.rep in
        let srep = self.rep in
        srep # prep };
    { forall p:Pqueue in pool, q:Pqueue in pool.
        p <> q -> p <> self -> q <> self ->
        let prep = p.rep in let qrep = q.rep in prep # qrep };
    { pqueuePub () };
    { let rep = self.rep in repClosed(rep) };
    { pqueueI () };

    var hd : Node in
    hd := self.head;
    if hd = null then
        { let rep = self.rep in repClosed(rep) };
        self.head := result;
        { self.head = result };
        { let hd = self.head in
          let rep = self.rep in hd in rep };
        { let hd = self.head in
          hd.sibling = null /\ hd.prev = null /\ hd.child = null };
    else
        var tmp : Node in
        tmp := link (self, hd, result);
        self.head := tmp;
        { let hd = self.head in
          let rep = self.rep in hd in rep };
    end;
    var sz : int in
    sz := self.size;
    self.size := sz + 1;

  meth combineAux (self:Pqueue+, handle:Node+) : Node+
    requires { self in pool }
    requires { self.size <> 0 }
    requires { let rep = self.rep in handle in rep }
    requires { handle.sibling <> null }
    requires { pqueuePub () }
    requires { pqueueI () }
    ensures  { pqueuePub () }
    ensures  { pqueueI () }
    ensures  { let rep = self.rep in result in rep }
    effects  { wr {self}`rep`prev, {self}`rep`sibling, {self}`rep`child, alloc;
                  /* {result}`prev, {result}`sibling, {result}`child, alloc; */
               rd {self}`rep`any }
  = var trees : NodeArray in
    var index : int in
    var current : Node in
    var tmp : Node in
    var fst : Node in
    var snd : Node in
    var i : int in
    var j : int in

    trees := new NodeArray[1024];
    trees[0] := handle; { trees[0] <> null };
    { forall p:NodeArray. p <> trees -> let s = old(p.slots) in s = p.slots };
    index := 1;
    current := handle.sibling;

    while (current <> null) do
      invariant { 1 <= index /\ let l = trees.length in index < l }
      invariant { forall k:int. 0 <= k -> k < index -> trees[k] <> null }
      invariant { let l = trees.length in
                  forall k:int. index <= k -> k < l -> trees[k] = null }
      invariant { forall k:int. 0 <= k -> k < index ->
                  let n = trees[k] in let rep = self.rep in n in rep }
      invariant { let rep = self.rep in current in rep }
      invariant { let rep = self.rep in repClosed (rep) }
      invariant { forall p:Node. p notin {self}`rep ->
                    let sib = old(p.sibling) in
                    let prev = old(p.prev) in
                    let child = old(p.child) in
                    p.sibling = sib /\ p.prev = prev /\ p.child = child }
      invariant { forall p:NodeArray. p <> trees ->
                    let slots = old(p.slots) in
                    let length = old(p.length) in
                    p.slots = slots /\ p.length = length }
      invariant { pqueuePub () }
      invariant { pqueueI () }

      assume { let l = trees.length in index < l-1 };

      trees[index] := current;
      tmp := current.prev;
      if (tmp <> null) then
          tmp.sibling := null;
      end;
      current := current.sibling;
      index := index + 1;      
    done;

    trees[index] := null;
    { let l = trees.length in index < l };

    i := 0; tmp := null;
    while ((i + 1) < index) do
      invariant { forall k:int. 0 <= k -> k < index -> trees[k] <> null }
      invariant { let l = trees.length in
                  forall k:int. index <= k -> k < l -> trees[k] = null }
      invariant { forall k:int. 0 <= k -> k < index ->
                    let n = trees[k] in let rep = self.rep in n in rep }
      invariant { forall p:Node. p notin {self}`rep ->
                    let sib = old(p.sibling) in
                    let prev = old(p.prev) in
                    let child = old(p.child) in
                    p.sibling = sib /\ p.prev = prev /\ p.child = child }
      invariant { forall p:NodeArray. p <> trees ->
                    let slots = old(p.slots) in
                    let length = old(p.length) in
                    p.slots = slots /\ p.length = length }
      invariant { pqueuePub () }
      invariant { pqueueI () }
      invariant { 0 <= i /\ i <= index }
      invariant { let rep = self.rep in tmp in rep }

      fst := trees[i];
      snd := trees[i+1];
      tmp := link(self, fst, snd);
      trees[i] := tmp;
      i := i + 2;
    done;

    j := i - 2;
    if (j >= 0 and j = index - 3) then
        { (j + 2) < index };
        fst := trees[j];
        snd := trees[j+2];
        tmp := link(self, fst, snd);
        trees[j] := tmp;
    end;

    while (2 <= j) do
      invariant { forall k:int. 0 <= k -> k < index -> trees[k] <> null }
      invariant { let l = trees.length in
                  forall k:int. index <= k -> k < l -> trees[k] = null }
      invariant { forall k:int. 0 <= k -> k < index ->
                    let n = trees[k] in let rep = self.rep in n in rep }
      invariant { forall p:Node. p notin {self}`rep ->
                    let sib = old(p.sibling) in
                    let prev = old(p.prev) in
                    let child = old(p.child) in
                    p.sibling = sib /\ p.prev = prev /\ p.child = child }
      invariant { forall p:NodeArray. p <> trees ->
                    let slots = old(p.slots) in
                    let length = old(p.length) in
                    p.slots = slots /\ p.length = length }
      invariant { -2 <= j /\ j < index }
      invariant { pqueuePub () }
      invariant { pqueueI () }

      fst := trees[j-2];
      snd := trees[j];
      tmp := link(self, fst, snd);
      trees[j-2] := tmp;
      j := j - 2;
    done;

    result := trees[0];

  meth combine (self:Pqueue+, handle:Node+) : Node+
    requires { self in pool }
    requires { let rep = self.rep in handle in rep }
    requires { pqueuePub () }
    requires { pqueueI () }
    requires { self.size <> 0 }
    ensures  { pqueueI () }
    ensures  { pqueuePub () }
    ensures  { let rep = self.rep in result in rep }
    ensures  { let ohd = old (self.head) in self.head = ohd }
    effects  { wr {self}`rep`child, {self}`rep`prev, {self}`rep`sibling, alloc;
                  /* {result}`child, {result}`prev, {result}`sibling, alloc; */
               rd {self}`rep`any }
  = var tmp : Node in
    tmp := handle.sibling;
    if (tmp = null) then
        result := handle;
    else
        result := combineAux (self, handle);
    end;

  meth deleteMin (self:Pqueue+) : Node+
    requires { pqueueI () } ensures { pqueueI () }
  = result := findMin (self);
    var tmp : Node in
    /* self.head.child = null */
    tmp := self.head;
    tmp := tmp.child;
    if (tmp = null) then
        assume { self.size = 1 };
        self.head := null;
    else
        assume { let sz = self.size in sz > 1 };
        tmp := combine(self, tmp);
        self.head := tmp;
    end;
    var sz : int in
    sz := self.size;
    self.size := sz - 1;

  meth decreaseKey (self:Pqueue+, handle:Node+, k:int) : unit
    requires { pqueueI () } ensures { pqueueI () }
  = var tmp : Node in
    var pos : Node in
    { let key = handle.key in key >= 0 };
    handle.key := k;
    tmp := self.head;
    if (handle <> tmp) then
        tmp := handle.sibling;
        if (tmp <> null) then
            pos := handle.prev;
            tmp.prev := pos;
        end;

        tmp := handle.prev;
        { let rep = self.rep in tmp in rep };
        if (tmp <> null) then
            pos := tmp.child;
            if (pos = handle) then
                pos := handle.sibling;
                tmp.child := pos;
            else
                pos := handle.sibling;
                { let rep = self.rep in pos in rep /\ tmp in rep };
                tmp.sibling := pos;
                { let rep = self.rep in let sib = tmp.sibling in sib in rep };
            end;
            { forall p:Node.
                let rep = self.rep in
                p notin rep -> let sib = old(p.sibling) in p.sibling = sib };
        end;

        handle.sibling := null;
        pos := self.head;
        { pos <> null };
        tmp := link(self, pos, handle);
        self.head := tmp;
    end;

end
