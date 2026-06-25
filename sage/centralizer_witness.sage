# Author: Carles Marin <karlesmarin@gmail.com> (with Claude, Anthropic, as assistant)
# Witness: centralizer of the simply-transitive T/I regular rep on 24 triads = dual group D12;
# PLR = that centralizer. Corroborates Lean Brick 3 (centralizer of regular rep = opposite regular rep).
R = Integers(12)
MAJ=[0,4,7]; MIN=[0,3,7]
def triad(root,kind):
    base=MAJ if kind=='M' else MIN
    return frozenset(R(root+i) for i in base)
triads=[triad(r,'M') for r in range(12)]+[triad(r,'m') for r in range(12)]
assert len(set(triads))==24
idx={t:i+1 for i,t in enumerate(triads)}
def perm_of(f): return [idx[frozenset(f(p) for p in t)] for t in triads]
T1=perm_of(lambda p:R(p+1)); I0=perm_of(lambda p:R(-p))
def classify(t):
    for r in range(12):
        if t==triad(r,'M'): return (r,'M')
        if t==triad(r,'m'): return (r,'m')
    raise Exception("nt")
def P_op(t):
    r,k=classify(t); return triad(r,'m' if k=='M' else 'M')
def L_op(t):
    r,k=classify(t); return triad((r+4)%12,'m') if k=='M' else triad((r-4)%12,'M')
def R_op(t):
    r,k=classify(t); return triad((r-3)%12,'m') if k=='M' else triad((r+3)%12,'M')
def perm_op(op): return [idx[op(t)] for t in triads]
Pp=perm_op(P_op); Lp=perm_op(L_op); Rp=perm_op(R_op)
def gp(img): return "PermList(%s)"%(img,)
ev=libgap.eval
ev("S:=SymmetricGroup(24)")
ev("T1:=%s"%gp(T1)); ev("I0:=%s"%gp(I0))
ev("TI:=Group(T1,I0)")
ev("Pp:=%s"%gp(Pp)); ev("Lp:=%s"%gp(Lp)); ev("Rp:=%s"%gp(Rp))
ev("PLR:=Group(Pp,Lp,Rp)")
ev("C:=Centralizer(S,TI)")
print("=== T/I on 24 triads ===")
print("|T/I| =", ev("Order(TI)"))
print("transitive?", ev("IsTransitive(TI,[1..24])"), " regular?", ev("IsRegular(TI,[1..24])"))
print("T/I struct:", ev("StructureDescription(TI)"))
print("=== Centralizer in S24 (the DUAL) ===")
print("|C| =", ev("Order(C)"), " struct:", ev("StructureDescription(C)"), " regular?", ev("IsRegular(C,[1..24])"))
print("=== PLR vs centralizer ===")
print("|PLR| =", ev("Order(PLR)"), " struct:", ev("StructureDescription(PLR)"))
print("PLR <= C?", ev("IsSubgroup(C,PLR)"), " PLR == C?", ev("PLR=C"))
print("Centralizer(S,PLR) == TI?", ev("Centralizer(S,PLR)=TI"))
print("=== 6-30 = (013679) restricted to its 12-form T/I orbit ===")
H=frozenset(R(x) for x in [0,1,3,6,7,9])
def img_set(f,S0): return frozenset(f(p) for p in S0)
seen=set(); orbit=[]
for j in range(12):
    for inv in [False,True]:
        f=(lambda p,j=j,inv=inv: R(-p+j) if inv else R(p+j))
        s=img_set(f,H)
        if s not in seen:
            seen.add(s); orbit.append(s)
oidx={s:i+1 for i,s in enumerate(orbit)}
print("orbit size:", len(orbit), "(expect 12: stabilizer={T0,T6}, |orbit|=24/2)")
def perm_on_orbit(f): return [oidx[img_set(f,s)] for s in orbit]
t1o=perm_on_orbit(lambda p:R(p+1)); i0o=perm_on_orbit(lambda p:R(-p))
n=len(orbit)
ev("So:=SymmetricGroup(%d)"%n)
ev("t1o:=%s"%gp(t1o)); ev("i0o:=%s"%gp(i0o))
ev("TIo:=Group(t1o,i0o)")
ev("Co:=Centralizer(So,TIo)")
print("|TI on orbit| =", ev("Order(TIo)"), " transitive?", ev("IsTransitive(TIo,[1..%d])"%n), " regular?", ev("IsRegular(TIo,[1..%d])"%n))
print("TI-on-orbit struct:", ev("StructureDescription(TIo)"))
print("|Centralizer on orbit (DUAL of 6-30)| =", ev("Order(Co)"), " struct:", ev("StructureDescription(Co)"))
print("Centralizer regular on orbit?", ev("IsRegular(Co,[1..%d])"%n))

# ===================== RESULTS (GAP, container cognitive_arch_sage, 2026-06-22) =====================
# NB: GAP names dihedral groups by ORDER. GAP "D24" = musicians' D12 (order 24); GAP "D12" = D6 (order 12).
#
# === T/I on 24 triads ===
# |T/I| = 24 ; transitive? true ; regular? true ; struct = D24 (=D12)
# === Centralizer in S24 (the DUAL) ===
# |C| = 24 ; struct = D24 (=D12) ; regular? true
# === PLR vs centralizer ===
# |PLR| = 24 ; struct = D24 (=D12)
# PLR <= C? true ; PLR == C? true ; Centralizer(S,PLR) == TI? true   <-- reciprocal duality, exact
# === 6-30 = (013679) on its 12-form T/I orbit ===
# orbit size = 12 (stabilizer {T0,T6}, 24/2)
# |TI on orbit| = 12 ; transitive/regular ; struct = D12 (=D6)
# |Centralizer on orbit (DUAL of 6-30)| = 12 ; struct = D12 (=D6) ; regular
# CONCLUSION: dual of 6-30 at reduced order is D6 (order 12). Matches the note's central claim.
