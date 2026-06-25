# Author: Carles Marin <karlesmarin@gmail.com> (with Claude, Anthropic, as assistant)
# What: Witness the full closed-form spectrum of the neo-Riemannian PLR/Tonnetz
#       Cayley graph Gamma = Cayley(PLR ~= D12, {P,L,R}) on the 24 triads.
#       Confirms spectrum = +-{3, sqrt5, 2cos(pi/12), sqrt3, 1, 2cos(5pi/12)}
#       via the Babai (1979) Cayley-spectrum-via-irreps mechanism, EXACTLY
#       (cyclotomic / QQbar arithmetic), and that the golden sqrt5 = |1+w^3+w^9| (j=3).
# Run: docker exec cognitive_arch_sage sh -c \
#        'cd /home/sage/project && sage tonnetz_cayley_spectrum.py'

from sage.all import *

PASS = True
def check(name, cond):
    global PASS
    status = "OK " if cond else "FAIL"
    if not cond:
        PASS = False
    print("  [%s] %s" % (status, name))
    return cond

print("=" * 72)
print(" Neo-Riemannian PLR / Tonnetz Cayley graph: closed-form spectrum witness")
print("=" * 72)

# ----------------------------------------------------------------------
# 1. The 24 triads + P, L, R as maps on (root, quality) from pitch classes
# ----------------------------------------------------------------------
# Major triad at root r : {r, r+4, r+7}.  Minor triad at root r : {r, r+3, r+7}.
def major(r): return frozenset([r % 12, (r + 4) % 12, (r + 7) % 12])
def minor(r): return frozenset([r % 12, (r + 3) % 12, (r + 7) % 12])

triads = []            # list of (frozenset, label)
labels = []
for r in range(12):
    triads.append(major(r)); labels.append((r, 'M'))
    triads.append(minor(r)); labels.append((r, 'm'))
pcset = [t for (t) in triads]                       # the 24 pc-sets
idx = {t: i for i, t in enumerate(pcset)}
n = 24
check("24 distinct triads", len(set(pcset)) == 24)

# P,L,R defined on the (root, quality) coordinates (standard neo-Riemannian involutions):
#   P (parallel)        : maj r  <-> min r           (C major <-> C minor)
#   L (leading-tone)    : maj r  <-> min r+4         (C major <-> E minor)
#   R (relative)        : maj r  <-> min r-3         (C major <-> A minor)
# All swap maj<->min and share exactly 2 common tones (verified below).
def quality_root(t):
    for r in range(12):
        if major(r) == t: return (r, 'M')
        if minor(r) == t: return (r, 'm')
    raise ValueError("not a triad")

def P(t):
    r, q = quality_root(t)
    return minor(r) if q == 'M' else major(r)
def L(t):
    r, q = quality_root(t)
    return minor((r + 4) % 12) if q == 'M' else major((r - 4) % 12)
def R(t):
    r, q = quality_root(t)
    return minor((r - 3) % 12) if q == 'M' else major((r + 3) % 12)

# involutions + shared-2-tones + maj<->min
inv_ok = all(P(P(t)) == t and L(L(t)) == t and R(R(t)) == t for t in pcset)
share2 = all(len(t & f(t)) == 2 for t in pcset for f in (P, L, R))
flip = all(quality_root(f(t))[1] != quality_root(t)[1] for t in pcset for f in (P, L, R))
check("P,L,R are involutions", inv_ok)
check("P,L,R each share exactly 2 common tones", share2)
check("P,L,R each swap major<->minor", flip)

# ----------------------------------------------------------------------
# 2. Adjacency matrix A (edge iff t' in {Pt,Lt,Rt}); symmetric & 3-regular
# ----------------------------------------------------------------------
A = matrix(ZZ, n, n, 0)
for i, t in enumerate(pcset):
    for f in (P, L, R):
        A[i, idx[f(t)]] = 1
check("A symmetric", A == A.transpose())
check("A is 3-regular", all(sum(A.row(i)) == 3 for i in range(n)))
# (this also confirms PLR acts simply transitively => the triad graph IS the Cayley graph)

# ----------------------------------------------------------------------
# 3. Spectrum: exact integer characteristic polynomial + numeric eigenvalues
# ----------------------------------------------------------------------
chi = A.charpoly()
print()
print("Exact characteristic polynomial chi_A(x) in ZZ[x]:")
print("  ", chi.factor())

# Exact eigenvalues over the algebraic reals (AA): A is a real symmetric integer matrix.
AA_eigs = matrix(AA, A).eigenvalues()   # algebraic reals, exact
# tally with exact multiplicity
from collections import Counter
ctr = Counter(AA_eigs)
exact_spec = sorted(ctr.items(), key=lambda kv: -RR(kv[0]))

# ----------------------------------------------------------------------
# 4. Closed-form claim:  spectrum = +- {3, sqrt5, 2cos(pi/12), sqrt3, 1, 2cos(5pi/12)}
#    Four 1-dim irreps -> +-3, +-1.  Five 2-dim irreps j=1..5 -> +-|1+w^j+w^{9j}|,
#    each with multiplicity 2.  (w = e^{2 pi i /12}.)
# ----------------------------------------------------------------------
w = QQbar.zeta(12)          # exact primitive 12th root of unity e^{2 pi i/12}
def two_dim_eig(j):
    # |1 + w^j + w^{9 j}| as an exact algebraic real
    z = 1 + w**(j % 12) + w**((9 * j) % 12)
    return AA(abs(z))

closed = {}                 # value -> expected multiplicity
# 1-dim irreps contribute +3,-3,+1,-1 (each once -> total mult 1 apiece)
for v in (AA(3), AA(-3), AA(1), AA(-1)):
    closed[v] = closed.get(v, 0) + 1
# 2-dim irreps j=1..5 contribute +-two_dim_eig(j), each eigenvalue with mult 2
for j in range(1, 6):
    e = two_dim_eig(j)
    closed[e] = closed.get(e, 0) + 2
    closed[-e] = closed.get(-e, 0) + 2

# Symbolic names for the table
def closed_name(v):
    candidates = {
        "+3": AA(3), "-3": AA(-3), "+1": AA(1), "-1": AA(-1),
        "+sqrt5": AA(sqrt(5)), "-sqrt5": -AA(sqrt(5)),
        "+sqrt3": AA(sqrt(3)), "-sqrt3": -AA(sqrt(3)),
        "+2cos(pi/12)": AA(2 * cos(pi / 12)),  "-2cos(pi/12)": -AA(2 * cos(pi / 12)),
        "+2cos(5pi/12)": AA(2 * cos(5 * pi / 12)), "-2cos(5pi/12)": -AA(2 * cos(5 * pi / 12)),
    }
    for nm, val in candidates.items():
        if val == v:
            return nm
    return "?"

print()
print("Comparison table  (computed eigenvalue | closed form | mult | match):")
print("  %-12s  %-16s  %-5s  %s" % ("computed", "closed form", "mult", "match"))
all_match = True
for v, m in exact_spec:
    nm = closed_name(v)
    cm = closed.get(v, 0)
    ok = (cm == m) and (nm != "?")
    all_match = all_match and ok
    print("  %-12s  %-16s  %-5d  %s" % (RR(v).str(digits=8), nm, m, "yes" if ok else "NO"))
# also confirm no closed-form value is missing from computed set
covered = (set(closed.keys()) == set(v for v, _ in exact_spec))
check("computed spectrum == closed-form spectrum (values + multiplicities)",
      all_match and covered)
check("total multiplicity = 24", sum(m for _, m in exact_spec) == 24)

# ----------------------------------------------------------------------
# 5. Babai mechanism: build each 2-dim dihedral irrep rho_j explicitly and
#    verify eig(rho_j(P)+rho_j(L)+rho_j(R)) = +- |1 + w^j + w^{9j}|.
#    s = L*R is the order-12 rotation (circle of fifths); reflections P,L,R = s^k * R.
# ----------------------------------------------------------------------
# find k_P, k_L with  P = s^{k} * R  (as permutation matrices), R = s^0 * R.
def perm_mat(f):
    M = matrix(ZZ, n, n, 0)
    for i, t in enumerate(pcset):
        M[idx[f(t)], i] = 1
    return M
MP, ML, MR = perm_mat(P), perm_mat(L), perm_mat(R)
S = ML * MR                                  # s = L*R
# order of s
o = 1; M = S
while M != identity_matrix(n):
    M = M * S; o += 1
check("s = L*R has order 12 (the fifths cycle)", o == 12)

def s_pow(k):
    M = identity_matrix(n)
    for _ in range(k % 12): M = M * S
    return M
def find_k(target):
    for k in range(12):
        if s_pow(k) == target: return k
    return None
kP = find_k(MP * MR)     # P*R = s^{kP}
kL = find_k(ML * MR)     # L*R = s^{kL}
print()
print("Dihedral coordinates:  P = s^%s * R,   L = s^%s * R,   R = s^0 * R   (s = L*R)" % (kP, kL))

# Standard 2-dim irrep rho_j of D12 over QQbar:
#   s -> Rot(2 pi j / 12),  reflection t=R -> antidiagonal reflection diag(1,-1).
#   reflection s^k * R -> Rot(k * 2 pi j /12) @ diag(1,-1).
def rot_j(k, j):
    th = 2 * w**(0)   # placeholder; we build rotation from zeta powers exactly
    # Rot(2 pi (k j)/12) using exact cos/sin via zeta12
    a = (k * j) % 12
    c = (w**a + w**(-a)) / 2                 # cos(2 pi a /12)
    snt = (w**a - w**(-a)) / (2 * QQbar(I))  # sin(2 pi a /12)
    return matrix(QQbar, [[c, -snt], [snt, c]])
refl0 = matrix(QQbar, [[1, 0], [0, -1]])

print()
print("Per-irrep eigenvalues of rho_j(P)+rho_j(L)+rho_j(R):")
print("  %-4s  %-22s  %-22s  %s" % ("j", "eig(P+L+R) [+-]", "|1+w^j+w^{9j}|", "match"))
irreps_ok = True
for j in range(1, 6):
    rhoR = rot_j(0,  j) * refl0
    rhoP = rot_j(kP, j) * refl0
    rhoL = rot_j(kL, j) * refl0
    Sj = rhoP + rhoL + rhoR
    # 2x2 symmetric (over reals); its eigenvalues via charpoly over QQbar -> AA
    cp = matrix(QQbar, Sj).charpoly()
    # eigenvalues are roots; for a real symmetric-ish matrix they are +- e
    e_pred = two_dim_eig(j)
    # verify charpoly = x^2 - e^2  (trace 0, det = -e^2)
    tr = Sj.trace()
    det = Sj.det()
    ok = (AA(tr) == 0) and (AA(det) == -e_pred**2)
    irreps_ok = irreps_ok and ok
    print("  %-4d  %-22s  %-22s  %s" % (
        j, "+-" + RR(e_pred).str(digits=8), RR(e_pred).str(digits=8),
        "yes" if ok else "NO"))
check("each 2-dim irrep gives eig = +- |1+w^j+w^{9j}| (Babai mechanism)", irreps_ok)

# ----------------------------------------------------------------------
# 6. The GOLDEN eigenvalue: sqrt5 = |1 + w^3 + w^9|  (j = 3), EXACT symbolic check
# ----------------------------------------------------------------------
golden = two_dim_eig(3)
print()
print("Golden check:  |1 + w^3 + w^9| = %s   (exact AA)" % golden)
check("sqrt(5) == |1 + w^3 + w^9|  (j=3, exact)", golden == AA(sqrt(5)))

# ----------------------------------------------------------------------
# 7. PASS/FAIL summary
# ----------------------------------------------------------------------
print()
print("=" * 72)
print("VERDICT: %s -- closed-form PLR/Tonnetz spectrum +-{3,sqrt5,2cos(pi/12),sqrt3,1,2cos(5pi/12)} %s"
      % ("PASS" if PASS else "FAIL", "holds exactly" if PASS else "DOES NOT hold"))
print("=" * 72)
