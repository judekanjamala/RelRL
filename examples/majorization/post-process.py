import sys
import re

m_pat = re.compile(r'let m \(s: state\).*$')
m_subst = (
    "let m (s: state) (x: int) : int"
    " diverges"
)

rel_m_pat = re.compile(r'\(int, int\).*$')
rel_m_subst = (
    "  (int, int) diverges"
)


with open(sys.argv[1], 'r') as f:
    for line in f:
        line = m_pat.sub(m_subst,line)
        line = rel_m_pat.sub(rel_m_subst,line)
        print(line,end='')
