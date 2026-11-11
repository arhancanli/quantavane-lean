# Independent exact check of the n = 12 angle certificate (11 Nov 2026). Written from the
# definitions, not from certify.py. Variables th(v;x,y) = angle at v in triangle vxy (unordered {x,y}).
# Valid facts for a strictly convex polygon with vertices 0..n-1 in cyclic order:
#  T(a,b,c): th(a;b,c) + th(b;a,c) + th(c;a,b) = 180
#  A(v,x,y,z): y strictly between x and z in the cyclic order seen from v  =>  th(v;x,z) = th(v;x,y) + th(v;y,z)
#  E(o,p,q) with |op| = |oq| (a hypothesis):  th(q;o,p) = th(p;o,q)
# Farkas: if  b.y - 180 * sum_j max(0, (A^T y)_j) > 0  then no 0 <= th <= 180 satisfies the rows.
import json, sys
from fractions import Fraction as F
n = 12
def th(v, x, y): return (v, min(x, y), max(x, y))
def between(v, x, y, z):
    px, py, pz = ((x - v) % n, (y - v) % n, (z - v) % n)
    return min(px, pz) < py < max(px, pz) and 0 not in (px, py, pz)
def row(lab, core):
    k = lab[0]
    if k == 'T':
        a, b, c = lab[1:]; assert len({a, b, c}) == 3
        return {th(a, b, c): 1, th(b, a, c): 1, th(c, a, b): 1}, 180
    if k == 'A':
        v, x, y, z = lab[1:]; assert len({v, x, y, z}) == 4 and between(v, x, y, z), lab
        return {th(v, x, z): 1, th(v, x, y): -1, th(v, y, z): -1}, 0
    if k == 'E':
        o, p, q = lab[1:]; assert (o, min(p, q), max(p, q)) in core, ('E row not a hypothesis', lab)
        return {th(q, o, p): 1, th(p, o, q): -1}, 0
    raise ValueError(lab)
def check(cert, core):
    core = {(o, min(p, q), max(p, q)) for _, o, p, q in core}
    tot = {}; by = F(0)
    for lab, yv in cert:
        y = F(yv); coeffs, rhs = row(lab, core)
        by += y * rhs
        for var, c in coeffs.items(): tot[var] = tot.get(var, 0) + y * c
    pos = sum(max(F(0), c) for c in tot.values())
    return by - 180 * pos, by, pos
d = json.loads(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'core1.cert')).readline())
gap, by, pos = check(d['y'], d['core'])
print('base core', d['core'], ': b.y =', by, ' 180*sum(pos) =', 180 * pos, ' margin =', gap, 'PASS' if gap > 0 else 'FAIL')
# all 24 dihedral images: relabel the certificate by g and check against the relabelled core
ok = 0
for refl in (False, True):
    for s in range(n):
        g = (lambda i, s=s, refl=refl: ((-i if refl else i) + s) % n)
        core = [['E', g(o), g(p), g(q)] for _, o, p, q in d['core']]
        cert = [[[lab[0]] + [g(t) for t in lab[1:]], yv] for lab, yv in d['y']]
        m, _, _ = check(cert, core); ok += m > 0
print('dihedral images passing:', ok, 'of 24')
# red control: drop one E row (the system must then lose infeasibility under this y)
bad = [c for c in d['y'] if c[0][0] != 'E' or c[0][1:] != d['core'][0][1:]]
print('red control (one hypothesis removed):', 'FAIL as expected' if check(bad, d['core'])[0] <= 0 else 'STILL PASSES (bad)')
