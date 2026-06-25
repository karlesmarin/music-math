# sc630_verify.sage — bulletproof witness for the 6-30 note's load-bearing facts.
# Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as assistant)
#
# Backs the §2 claims of paper/sixthirty_note.md with a re-runnable computation (not prose):
#   (1) interval vector of 6-30 = (013679);
#   (2) EXACT T/I-stabilizer = {T0, T6}, order 2, ZERO inversions  ⇒  transpositional symmetry only;
#   (3) 6-30 is NOT inversionally symmetric: its inversion is not a transposition of it
#       (Tn-type(A) != Tn-type(I A))  ⇒  the 6-30A / 6-30B distinction;
#   (4) the inversion lands on (0,1,4,6,7,10) = FN2011's "Major Triad Tritone Mixture".
# WRITEUP RULE this enforces: claim T6-symmetry (stab={T0,T6}) ONLY, never inversional symmetry.

n = 12
A = frozenset([0, 1, 3, 6, 7, 9])          # prime form of set class 6-30

def Tn(k, S):  return frozenset((x + k) % n for x in S)
def In(k, S):  return frozenset((k - x) % n for x in S)   # I_k(x) = k - x

def interval_vector(S):
    iv = [0]*6
    L = sorted(S)
    for i in range(len(L)):
        for j in range(i+1, len(L)):
            d = (L[j] - L[i]) % n
            ic = min(d, n - d)                # interval class 1..6
            iv[ic-1] += 1
    return iv

def tn_type(S):
    # canonical transposition (Tn-type): the lexicographically least transposition, as a 0-based tuple
    best = None
    for k in range(n):
        cand = tuple(sorted(Tn(k, S)))
        cand = tuple((x - cand[0]) % n for x in cand)
        cand = tuple(sorted(cand))
        if best is None or cand < best:
            best = cand
    return best

print("A = 6-30 =", tuple(sorted(A)))
print("interval vector IV(A) =", interval_vector(A))

T_stab = [k for k in range(n) if Tn(k, A) == A]
I_stab = [k for k in range(n) if In(k, A) == A]
print("transposition stabilizer  {k : T_k A = A} =", ["T%d" % k for k in T_stab])
print("inversion stabilizer      {k : I_k A = A} =", ["I%d" % k for k in I_stab])
print("=> |T/I-stabilizer| =", len(T_stab) + len(I_stab),
      "; inversions in stabilizer:", len(I_stab))

B = In(0, A)                                  # the inversion (about 0)
print()
print("inversion I_0(A) =", tuple(sorted(B)))
is_transpose = any(Tn(k, A) == B for k in range(n))
print("is I_0(A) a transposition of A?", is_transpose, " (False => NOT inversionally symmetric)")
print("Tn-type(A)      =", tn_type(A))
print("Tn-type(I_0 A)  =", tn_type(B))
print("Tn-types differ (6-30A vs 6-30B):", tn_type(A) != tn_type(B))
FN = frozenset([0, 1, 4, 6, 7, 10])           # FN2011 "Major Triad Tritone Mixture"
print("I_0(A) is a transposition of FN2011 (0,1,4,6,7,10):",
      any(Tn(k, B) == FN for k in range(n)),
      "; same Tn-type:", tn_type(B) == tn_type(FN))

# Expected (anchored 2026-06-23):
#   IV = [2, 2, 4, 2, 2, 3] ; stabilizer = {T0, T6}, order 2, 0 inversions ;
#   I_0(A) = (0,1,4,6,7,10), NOT a transposition of A ; Tn-types differ ; matches FN2011 set.
