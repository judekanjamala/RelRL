import sys
import re

multiply_pat = re.compile(r'let multiply \(s: state\).*$')
multiply_subst = (
    "let multiply (s: state) (n: int) (m: int) : int"
    " diverges"
)

rel_multiply_pat = re.compile(r'\(int, int\).*$')
rel_multiply_subst = "   (int, int) diverges"

with open(sys.argv[1], 'r') as f:
    for line in f:
        line = multiply_pat.sub(multiply_subst,line)
        line = rel_multiply_pat.sub(rel_multiply_subst,line)
        print(line,end='')
