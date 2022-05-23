import sys
import re

axiom_pat = re.compile(r'axiom\s*(\w+)\s*=')
lemma_pat = re.compile(r'lemma\s*(\w+)\s*=')

# count_female_pat = re.compile(r'let count_female \(s: state\).*$')
# count_female_subst = (
#     "let count_female (s: state) (people: reference) : int"
#     " diverges"
# )

diverges_pat = re.compile(r'@\s*diverge')


with open(sys.argv[1], 'r') as f:
    for line in f:
        line = axiom_pat.sub(r"axiom \1 :",line)
        line = lemma_pat.sub(r"lemma \1 :",line)
        # line = count_female_pat.sub(count_female_subst,line)
        line = diverges_pat.sub(' diverges',line)
        print(line,end='')
