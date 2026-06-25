# verify_formulas.py — independent computational audit of FORMULAS.md numeric claims.
# Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)
# What: re-derives each numeric claim in research/music-math/FORMULAS.md from scratch
#       (Sage/GAP), printing MATCH/MISMATCH against the registry's stated value.
# Run:  docker exec cognitive_arch_sage sh -c 'cd /home/sage/project && sage verify_formulas.py'

from itertools import combinations
from sage.all import gap, libgap, SymmetricGroup, PermutationGroup, continued_fraction, log, RR, Rational

n = 12
def Tn(k, S): return frozenset((x + k) % n for x in S)
def In(k, S): return frozenset((k - x) % n for x in S)   # I_k(x)=k-x

def iv(S):
    v=[0]*6; L=sorted(S)
    for i in range(len(L)):
        for j in range(i+1,len(L)):
            d=(L[j]-L[i])%n; ic=min(d,n-d); v[ic-1]+=1
    return v

def forte_prime(S, group="TI"):
    # Rahn-style normal/prime form: choose the most-packed-to-left rotation, incl. inversion if TI.
    cands=[]
    sets=[Tn(k,S) for k in range(n)]
    if group=="TI":
        sets+= [Tn(k,In(0,S)) for k in range(n)]
    for X in sets:
        L=sorted(X); L0=tuple((x-L[0])%n for x in L)
        cands.append(tuple(sorted(L0)))
    # most compact: minimize from the right (Rahn), tie-break lexicographically
    def key(t):
        return (t[-1],)+tuple(t)  # smallest span first, then lex
    return min(cands,key=key)

results=[]
def verdict(label, ok, got, exp):
    tag="MATCH" if ok else "MISMATCH"
    results.append((label,tag,got,exp))
    print(f"  [{tag}] {label}\n      got={got}\n      exp={exp}")

print("="*70); print("CLAIM 1 — set class 6-30"); print("="*70)
A=frozenset([0,1,3,6,7,9]); P=frozenset([0,1,4,6,7,10])
iA=iv(A)
verdict("6-30 interval vector [2,2,4,2,2,3]", iA==[2,2,4,2,2,3], iA, [2,2,4,2,2,3])
pfA=forte_prime(A); pfP=forte_prime(P)
verdict("Forte prime of {0,1,3,6,7,9} and Petrushka {0,1,4,6,7,10} same TI class",
        pfA==pfP, (pfA,pfP), "equal")
# T/I stabilizer
stab=[];
for k in range(n):
    if Tn(k,A)==A: stab.append(("T",k))
    if In(k,A)==A: stab.append(("I",k))
inv_count=sum(1 for t in stab if t[0]=="I")
verdict("T/I-stabilizer of 6-30 = {T0,T6}, order 2, 0 inversions",
        sorted(stab)==[("T",0),("T",6)] and inv_count==0, (sorted(stab),inv_count), "{T0,T6}, 0 inv")
# orbit size under TI
orbit=set()
for k in range(n):
    orbit.add(tuple(sorted(Tn(k,A)))); orbit.add(tuple(sorted(In(k,A))))
verdict("T/I orbit size = 12", len(orbit)==12, len(orbit), 12)
# centralizer (dual) of T/I acting on the 12-orbit, structure D6
orb=sorted(orbit); idx={s:i for i,s in enumerate(orb)}; m=len(orb)
def perm_T(k):
    return [idx[tuple(sorted(Tn(k,frozenset(s))))]+1 for s in orb]
def perm_I(k):
    return [idx[tuple(sorted(In(k,frozenset(s))))]+1 for s in orb]
Sm=SymmetricGroup(m)
gens=[Sm(perm_T(1)), Sm(perm_I(0))]
TIgrp=Sm.subgroup(gens)
# centralizer in S_m
Cent=Sm.centralizer(TIgrp)
sd=libgap(Cent).StructureDescription().sage()
verdict("centralizer(T/I) on 12-orbit: order 12, structure D6",
        Cent.order()==12 and sd in ("D12","D6"), (Cent.order(),sd), "(12, D6 i.e. dihedral order12)")
# 6-30 subset of an octatonic (8-28) collection
oct1=frozenset([0,1,3,4,6,7,9,10])
sub_ok=any(A.issubset(Tn(k,oct1)) or A.issubset(In(k,oct1)) for k in range(n))
verdict("6-30 subset of octatonic 8-28", sub_ok, sub_ok, True)

print("="*70); print("CLAIM 2 — central self-dual counts (A032239)"); print("="*70)
def setclass_reps(card):
    seen=set(); reps=[]
    for c in combinations(range(n),card):
        S=frozenset(c)
        if S in seen: continue
        orb=set()
        for k in range(n):
            orb.add(frozenset(Tn(k,S))); orb.add(frozenset(In(k,S)))
        seen|=orb; reps.append(S)
    return reps
def central_selfdual_count(nn):
    # count set classes (over all cardinalities) whose T/I stabilizer is EXACTLY {T0, T_{n/2}}
    global n
    n=nn; half=nn//2; cnt=0
    seen=set()
    for card in range(0,nn+1):
        for c in combinations(range(nn),card):
            S=frozenset(c)
            if S in seen: continue
            orb=set()
            for k in range(nn):
                orb.add(frozenset((x+k)%nn for x in S)); orb.add(frozenset((k-x)%nn for x in S))
            seen|=orb
            stab=set()
            for k in range(nn):
                if frozenset((x+k)%nn for x in S)==S: stab.add(("T",k))
                if frozenset((k-x)%nn for x in S)==S: stab.add(("I",k))
            if stab=={("T",0),("T",half)}:
                cnt+=1
    return cnt
exp_map={6:0,8:0,10:0,12:1,14:2,16:6,18:14}
for nn in [6,8,10,12,14,16,18]:
    got=central_selfdual_count(nn)
    verdict(f"central self-dual count n={nn}", got==exp_map[nn], got, exp_map[nn])
n=12
# OEIS A032239 cross-check m=6..9 -> 1,2,6,14
verdict("equals A032239(m=6..9)=1,2,6,14",
        [central_selfdual_count(2*m) for m in [6,7,8,9]]==[1,2,6,14],
        [central_selfdual_count(2*m) for m in [6,7,8,9]], [1,2,6,14])
n=12

print("="*70); print("CLAIM 3 — CFS duality on 24 triads"); print("="*70)
# triads: (root, isMajor). major r={r,r+4,r+7}, minor r={r,r+3,r+7}
triads=[(r,True) for r in range(12)]+[(r,False) for r in range(12)]
ti={t:i for i,t in enumerate(triads)}
def Tact(k,t): return ((t[0]+k)%12, t[1])
def Iact(j,t): # I_j(x)=j-x ; flips quality. sr_j • (x,b)=(-x-j-7,not b) per A.1
    return ((-t[0]-j-7)%12, not t[1])
ST=SymmetricGroup(24)
gT=ST([ti[Tact(1,t)]+1 for t in triads])
gI=ST([ti[Iact(0,t)]+1 for t in triads])
TIg=ST.subgroup([gT,gI])
sdTI=libgap(TIg).StructureDescription().sage()
# simply transitive: order 24 and transitive with trivial point-stab
verdict("T/I on 24 triads: order 24", TIg.order()==24, TIg.order(),24)
verdict("T/I simply transitive", TIg.is_transitive() and TIg.order()==24, (TIg.is_transitive(),TIg.order()), "(True,24)")
verdict("T/I ~ D12 (GAP D24)", sdTI=="D24", sdTI, "D24")
# PLR
def P(t): return (t[0], not t[1])
def L(t): return ((t[0]+4)%12, False) if t[1] else ((t[0]-4)%12, True)
def R(t): return ((t[0]-3)%12, False) if t[1] else ((t[0]+3)%12, True)
gP=ST([ti[P(t)]+1 for t in triads]); gL=ST([ti[L(t)]+1 for t in triads]); gR=ST([ti[R(t)]+1 for t in triads])
PLR=ST.subgroup([gP,gL,gR])
verdict("|PLR| = 24", PLR.order()==24, PLR.order(),24)
CentTI=ST.centralizer(TIg)
sdC=libgap(CentTI).StructureDescription().sage()
verdict("centralizer(T/I) in S24: order 24 ~ D12", CentTI.order()==24 and sdC=="D24",(CentTI.order(),sdC),"(24,D24)")
verdict("PLR == centralizer(T/I) exactly", PLR==CentTI, PLR==CentTI, True)

print("="*70); print("CLAIM 4 — homometry 4-Z15 / 4-Z29"); print("="*70)
n=12
z15=frozenset([0,1,4,6]); z29=frozenset([0,1,3,7])
verdict("4-Z15 and 4-Z29 same interval vector", iv(z15)==iv(z29), (iv(z15),iv(z29)), "equal [1,1,1,1,1,1]")
same_class = forte_prime(z15)==forte_prime(z29)
verdict("4-Z15 and 4-Z29 NOT T/I related (different set classes)", not same_class,
        (forte_prime(z15),forte_prime(z29)), "different")

print("="*70); print("CLAIM 5 — diatonic Myhill/ME spectra"); print("="*70)
diatonic=[0,2,4,5,7,9,11]
def generic_spectrum(scale,k):
    d=len(scale); sizes=set()
    for i in range(d):
        sizes.add((scale[(i+k)%d]-scale[i])%12)
    return sizes
spec=[sorted(generic_spectrum(diatonic,k)) for k in range(1,7)]
exp_spec=[[1,2],[3,4],[5,6],[6,7],[8,9],[10,11]]
verdict("diatonic generic spectra k=1..6", spec==exp_spec, spec, exp_spec)
all_card2=all(len(s)==2 for s in spec)
verdict("each diatonic generic spectrum has card 2 (Myhill)", all_card2, [len(s) for s in spec], "all 2")
wt=[0,2,4,6,8,10]
wts=[sorted(generic_spectrum(wt,k)) for k in range(1,6)]
verdict("whole-tone generic step (k=1) = {2}", generic_spectrum(wt,1)=={2}, sorted(generic_spectrum(wt,1)), [2])
# deep scale IVraw = 2*IV ; claim [4,10,8,6,12,2]
ivraw=[2*x for x in iv(frozenset(diatonic))]
verdict("diatonic IVraw = [4,10,8,6,12,2]", ivraw==[4,10,8,6,12,2], ivraw, [4,10,8,6,12,2])

print("="*70); print("CLAIM 6 — three-gap in Z12"); print("="*70)
def stack(start,g,d):
    return [ (start+i*g)%12 for i in range(d) ]
def step_sizes(points):
    pts=sorted(set(points)); m=len(pts); sizes=set()
    for i in range(m):
        sizes.add((pts[(i+1)%m]-pts[i])%12)
    return sizes
cases={"stack(0,7,5)":(stack(0,7,5),{2,3}),
       "stack(0,7,7)":(stack(0,7,7),{1,2}),
       "stack(0,7,6)":(stack(0,7,6),{1,2,3}),
       "stack(0,5,6)":(stack(0,5,6),None)}
verdict("stack(0,7,5) sizes {2,3}", step_sizes(stack(0,7,5))=={2,3}, sorted(step_sizes(stack(0,7,5))),[2,3])
verdict("stack(0,7,7) sizes {1,2}", step_sizes(stack(0,7,7))=={1,2}, sorted(step_sizes(stack(0,7,7))),[1,2])
verdict("stack(0,7,6) sizes {1,2,3}", step_sizes(stack(0,7,6))=={1,2,3}, sorted(step_sizes(stack(0,7,6))),[1,2,3])
verdict("stack(0,5,6) has 3 sizes", len(step_sizes(stack(0,5,6)))==3, sorted(step_sizes(stack(0,5,6))),"3 sizes")
# general bound
maxsz=0; worst=None
for g in range(12):
    for d in range(1,13):
        c=len(step_sizes(stack(0,g,d)))
        if c>maxsz: maxsz=c; worst=(g,d)
verdict("three-gap bound: max #sizes over all g,d <= 3", maxsz<=3, (maxsz,worst), "<=3")

print("="*70); print("CLAIM 7 — temperament vals/monzos"); print("="*70)
def pair(v,m): return sum(a*b for a,b in zip(v,m))
v12=[12,19,28]; syntonic=[-4,4,-1]; pc=[-19,12,0]
verdict("v12 tempers syntonic comma (=0)", pair(v12,syntonic)==0, pair(v12,syntonic),0)
verdict("v12 tempers Pythagorean comma (=0)", pair(v12,pc)==0, pair(v12,pc),0)
v5=[5,8]; v7=[7,11]; pc2=[-19,12]
verdict("v5 on Pythagorean = 1 (nonzero)", pair(v5,pc2)==1, pair(v5,pc2),1)
verdict("v7 on Pythagorean = -1 (nonzero)", pair(v7,pc2)==-1, pair(v7,pc2),-1)
# 3-limit: kernel of <12,19| = Z*(-19,12)
from sage.all import matrix, ZZ
Mv=matrix(ZZ,[[12,19]])
K=Mv.right_kernel().basis()
verdict("kernel of <12,19| = Z*(-19,12)", any(tuple(b)==(-19,12) or tuple(b)==(19,-12) for b in K), [tuple(b) for b in K], "(-19,12)")

print("="*70); print("CLAIM 8 — continued fraction log2(3/2)"); print("="*70)
val=log(Rational(3)/Rational(2),2)
cf=continued_fraction(RR(val))
quots=list(cf.quotients())[:8]
verdict("log2(3/2) CF starts [0;1,1,2,2,3,1,5,...]",
        quots[:8]==[0,1,1,2,2,3,1,5], quots[:8], [0,1,1,2,2,3,1,5])
convs=[cf.convergent(i) for i in range(8)]
conv_set=set((c.numerator(),c.denominator()) for c in convs)
want={(1,2),(3,5),(7,12),(24,41),(31,53)}
verdict("convergents include 1/2,3/5,7/12,24/41,31/53",
        want.issubset(conv_set), sorted(conv_set), sorted(want))

print("="*70); print("CLAIM 9 — Balzano Z12 = Z3 x Z4 (CRT)"); print("="*70)
from sage.all import gcd, CyclicPermutationGroup, AbelianGroup
g34=gcd(3,4)
# build iso explicitly: phi(x)=(x%3,x%4) bijective?
img=set((x%3,x%4) for x in range(12))
verdict("CRT gcd(3,4)=1", g34==1, int(g34),1)
verdict("x->(x%3,x%4) is a bijection Z12->Z3xZ4", len(img)==12, len(img),12)
# GAP structure check
G12=libgap.CyclicGroup(12); G3=libgap.CyclicGroup(3); G4=libgap.CyclicGroup(4)
GD=libgap.DirectProduct(G3,G4)
verdict("Z12 ~ Z3 x Z4 (GAP iso)", bool(libgap.IsomorphismGroups(G12,GD)!=libgap.eval("fail")),
        str(libgap(GD).StructureDescription()), "C12")

print("\n"+"="*70); print("SUMMARY"); print("="*70)
mismatches=[r for r in results if r[1]=="MISMATCH"]
print(f"Total checks: {len(results)}  MATCH: {len(results)-len(mismatches)}  MISMATCH: {len(mismatches)}")
if mismatches:
    print("\n*** MISMATCHES (errors to fix) ***")
    for lbl,tag,got,exp in mismatches:
        print(f"  - {lbl}: got={got} expected={exp}")
else:
    print("ALL CLAIMS MATCH.")
