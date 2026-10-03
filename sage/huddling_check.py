"""Exact cyclotomic-field cross-check, independent of the interval-vector formula.

Run: sage -python sage/huddling_check.py
The algebraic-real comparisons use Sage's AA field, not rounded complex numbers.
"""
from itertools import combinations
import json
from sage.all import AA, QQbar, CyclotomicField

field = CyclotomicField(12)
zeta = field.gen()
embedding = field.hom([QQbar.zeta(12)], QQbar)


def power(a, t):
    coefficient = sum((zeta ** (-t*x) for x in a), field.zero())
    return AA(embedding(coefficient * coefficient.conjugate()))


def orbit(a):
    return {tuple(sorted((x+t) % 12 for x in a)) for t in range(12)}


rows = []
for k in range(13):
    reference = tuple(range(k))
    peak = power(reference, 1)
    maximizers = set()
    for a in combinations(range(12), k):
        value = power(a, 1)
        assert value <= peak, (k, a)
        if value == peak:
            maximizers.add(a)
    assert maximizers == orbit(reference), k
    rows.append({"cardinality": k, "maximizers": len(maximizers)})

diatonic = (0, 2, 4, 5, 7, 9, 11)
peak = power(diatonic, 5)
assert peak == 7 + 4 * AA(3).sqrt()
fifth_maximizers = set()
for a in combinations(range(12), 7):
    value = power(a, 5)
    assert value <= peak, a
    if value == peak:
        fifth_maximizers.add(a)
assert fifth_maximizers == orbit(diatonic)
print(json.dumps({"arithmetic": "Q(zeta_12) and exact algebraic reals AA",
                  "huddling_subsets_checked": 4096, "cardinalities": rows,
                  "diatonic_seven_note_sets_checked": 792,
                  "diatonic_a5_power": "7 + 4 sqrt(3)",
                  "diatonic_maximizers": len(fifth_maximizers)}, indent=2))
