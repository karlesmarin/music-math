# sixthirty.sage — chase the (0,1,3,6,7,9) anomaly: Forte 6-30, uniqueness, dual group, generalization.
# Author: Carles Marin <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)
#
# Finding: a set class is "intermediate self-dual" (regular T/I action on an orbit of size n, with a
# regular order-n dual) IFF its T/I-stabilizer equals the CENTER {T0, T_{n/2}} of the dihedral group
# (n even). Such a set is T_{n/2}-invariant with no other T/I symmetry. We (1) detail the Z/12 case
# (= Forte 6-30, dual group structure), and (2) generalize: enumerate ONLY the T_{n/2}-invariant sets
# (unions of the n/2 central pairs {x, x+n/2}, so just 2^{n/2} candidates) and count center-stabilized
# classes per n -- cheap even for n=24.

def Tk(n, S, k): return frozenset((x + k) % n for x in S)
def Ik(n, S, k): return frozenset((-x + k) % n for x in S)
def canon(n, S):
    best = None
    for k in range(n):
        for t in (tuple(sorted(Tk(n,S,k))), tuple(sorted(Ik(n,S,k)))):
            if best is None or t < best: best = t
    return best
def stab(n, S):
    s = []
    for k in range(n):
        if Tk(n,S,k)==S: s.append(('T',k))
        if Ik(n,S,k)==S: s.append(('I',k))
    return s
def ivec(n, S):
    L = sorted(S); v = [0]*(n//2 + 1)
    for i in range(len(L)):
        for j in range(i+1, len(L)):
            d = (L[j]-L[i]) % n; v[min(d, n-d)] += 1
    return v[1:]

def center_classes(n):
    """Set classes whose T/I-stabilizer is EXACTLY the center {T0, T_{n/2}} (n even)."""
    half = n//2
    center = {('T',0), ('T',half)}
    pairs = [frozenset([x, (x+half)%n]) for x in range(half)]   # the n/2 central pairs
    seen = {}
    for mask in range(1, 1 << half):                            # nonempty unions of central pairs
        S = frozenset().union(*[pairs[i] for i in range(half) if mask & (1<<i)])
        if len(S) == n: continue
        cn = canon(n, S)
        if cn not in seen and set(stab(n, S)) == center:
            seen[cn] = S
    return seen

# (1) Z/12 detail: 6-30 + its dual group
n = 12; S = frozenset([0,1,3,6,7,9])
print("=== Z/12 detail: (0,1,3,6,7,9) ===")
print("stabilizer:", stab(n,S), "  (center = [T0,T6])")
print("interval vector:", ivec(n,S), "  (Forte 6-30 IV is 224223)")
orbit = sorted({tuple(sorted(Tk(n,S,k))) for k in range(n)} | {tuple(sorted(Ik(n,S,k))) for k in range(n)})
idx = {o:i+1 for i,o in enumerate(orbit)}; m = len(orbit)
Sg = SymmetricGroup(m)
gens = [Sg([idx[tuple(sorted(Tk(n,frozenset(o),1)))] for o in orbit]),
        Sg([idx[tuple(sorted(Ik(n,frozenset(o),0)))] for o in orbit])]
G = Sg.subgroup(gens); C = Sg._gap_().Centralizer(G._gap_())
print("orbit size:", m)
print("T/I-image : order", G.order(), " =", G._gap_().StructureDescription())
print("dual (C)  : order", Integer(C.Order()), " =", C.StructureDescription())

# (2) generalization across even n
print("\n=== center-stabilized classes per even n (the 'intermediate self-dual' classes) ===")
for n in [8, 10, 12, 14, 16, 18, 20, 24]:
    cc = center_classes(n)
    reps = sorted(cc.keys(), key=lambda t:(len(t), t))
    print("n=%2d : count=%d %s" % (n, len(reps), [r for r in reps][:6]))
