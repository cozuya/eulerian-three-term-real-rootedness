"""Independent finite convention checks; not a proof dependency."""
from collections import Counter
from itertools import permutations
import json
from pathlib import Path
import sys
import sympy as s

x, b, c = s.symbols('x b c')
A = [s.Poly(1, x), s.Poly(1, x)]
for n in range(1, 7):
    A.append(s.Poly((1+n*x)*A[n].as_expr()
                     + x*(1-x)*A[n].diff().as_expr(), x))

records = []
for n in range(8):
    counts = Counter(sum(pi[i] > pi[i+1] for i in range(n-1))
                     for pi in permutations(range(n)))
    enumerated = s.Poly(sum(number*x**descents
                           for descents, number in counts.items()), x)
    assert enumerated == A[n]
    records.append({'n': n, 'permutations': sum(counts.values()),
                    'coefficients_ascending': [int(A[n].nth(i))
                                                for i in range(A[n].degree()+1)],
                    'recurrence_equals_definition': True})

P3 = A[3].as_expr() + b*A[2].as_expr() + c*A[1].as_expr()
assert s.expand(P3 - (x*x+(b+4)*x+1+b+c)) == 0
assert s.discriminant(P3, x) == b*b+4*b+12-4*c
assert s.expand(P3.subs(c,b*b/4+b+3)-(x+b/2+2)**2) == 0

output = {'python': sys.version, 'sympy': s.__version__,
          'permutation_definition_checks': records,
          'P3_discriminant': str(s.discriminant(P3,x)),
          'boundary_factorization': '(x+b/2+2)^2',
          'all_passed': True}
Path(__file__).with_suffix('.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps(output, indent=2))
