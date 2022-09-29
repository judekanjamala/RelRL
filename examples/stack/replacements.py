import sys
import re

stackRep_pat = re.compile(r'predicate\s*stackRep.*$')
stackRep_subst = (
    "predicate stackRep (s: state) (xs: intList) (n: reference) =\n"
    "   match xs with Nil -> n = null\n"
    "   | Cons h t -> hasNodeType s n /\\ isAllocated s n /\\\n"
    "     isAllocated s s.heap.car[n] /\\\n"
    "     s.heap.cell_value[s.heap.car[n]] = h /\\\n"
    "     stackRep s t s.heap.cdr[n] end\n\n"
    "lemma stackRep_mono : forall xs. forall n s s'.\n"
    "  (forall p:reference. p \\: s.alloct ->\n"
    "     p \\: s'.alloct /\\ s'.alloct[p] = s.alloct[p]) ->\n"
    "  (forall p:reference. hasNodeType s p -> isAllocated s p ->\n"
    "     s.heap.car[p] = s'.heap.car[p] /\\\n"
    "     s.heap.cdr[p] = s'.heap.cdr[p]) ->\n"
    "  (forall p:reference. hasCellType s p -> isAllocated s p ->\n"
    "     s.heap.cell_value[p] = s'.heap.cell_value[p]) ->\n"
    "  stackRep s xs n -> stackRep s' xs n\n\n"
    "lemma stackRep_agree : forall xs. forall s t pi n.\n"
    "  okRefperm s t pi ->\n"
    "  PreRefperm.identity pi s.alloct.M.domain t.alloct.M.domain ->\n"
    "  PreRefperm.idRgn pi s.pool t.pool ->\n"
    "  s.maxSize = t.maxSize ->\n"
    "  agree_allfields s t pi (Rgn.union s.pool (img_rep s s.pool)) ->\n"
    "  Rgn.mem n (img_rep s s.pool) ->\n"
    "  Rgn.subset (img_cdr s (img_rep s s.pool)) (img_rep s s.pool) ->\n"
    "  Rgn.subset (img_car s (img_rep s s.pool)) (img_rep s s.pool) ->\n"
    "  stackRep s xs n -> stackRep t xs n\n\n"
)

with open(sys.argv[1], 'r') as f:
    for line in f:
        line = stackRep_pat.sub(stackRep_subst, line)
        print(line, end='')

