# tisetclasses.py — verifies the T/I set-class counts + the 6-30 uniqueness cited in the corpus paper.
# Author: Carles Marin <karlesmarin@gmail.com> (Claude, Anthropic, as AI assistant).
# Confirms: 224 T/I set classes total (223 nonempty, 222 nontrivial); EXACTLY ONE nontrivial class has
# T/I-stabilizer = {0,6} and no inversion symmetry = Forte 6-30 (the Petrushka set class).
from itertools import combinations
n=12
def Tk(S,k): return frozenset((x+k)%n for x in S)
def I(S):    return frozenset((-x)%n for x in S)
def orbit(S):
    R=set()
    for k in range(n):
        R.add(Tk(S,k)); R.add(I(Tk(S,k)))
    return R
# enumerate all T/I set classes (canonical rep = min orbit)
seen=set(); classes=[]
for r in range(0,n+1):
    for c in combinations(range(n),r):
        S=frozenset(c)
        if S in seen: continue
        orb=orbit(S)
        seen|=orb
        classes.append((r,min(orb)))
total=len(classes)
nonempty=[c for c in classes if c[0]>0]
nontrivial=[c for c in classes if 0<c[0]<n]   # exclude empty and full aggregate
print(f"T/I set classes (incl empty & full): {total}")
print(f"  nonempty: {len(nonempty)}")
print(f"  nontrivial (excl empty AND full): {len(nontrivial)}")
# stabilizer in T/I of a set class: count which classes have stab_T exactly {0,6} and no inversion symmetry
def stabT(S):  return [k for k in range(n) if Tk(S,k)==S]
def hasInvSym(S): return any(Tk(I(S),k)==S for k in range(n))
matches=[]
for r,rep in classes:
    if 0<r<n and set(stabT(rep))=={0,6} and not hasInvSym(rep):
        matches.append((r,sorted(rep)))
print(f"\nclasses with stab_T == exactly {{0,6}} and NO inversion symmetry: {len(matches)}")
for r,S in matches: print("   ",r,S)
