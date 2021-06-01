import sys
import re

fact_pat = re.compile(r'let fact \(s: state\).*$')
fact_subst = "let fact (s: state) (n: int) : int diverges"

rel_fact_pat = re.compile(r'\(int, int\).*$')
rel_fact_subst = "  (int, int) diverges"

with open(sys.argv[1], 'r') as f:
    for line in f:
        line = fact_pat.sub(fact_subst,line)
        line = rel_fact_pat.sub(rel_fact_subst,line)
        print(line,end='')
