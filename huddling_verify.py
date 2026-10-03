"""Independent exact Z12 census for Huddling and the diatonic energy connection.

This checks the mathematics with integer arithmetic in Z[sqrt(3)].
It is a verification aid; the Lean proofs are the formal artifact.
"""
from collections import Counter
from itertools import combinations
import json


def sign_sqrt3(p, q):
    """Sign of p + q sqrt(3), without floating point."""
    if q == 0:
        return (p > 0) - (p < 0)
    if p == 0 or (p > 0) == (q > 0):
        return (q > 0) - (q < 0)
    difference = p * p - 3 * q * q
    return ((difference > 0) - (difference < 0)) * ((p > 0) - (p < 0))


def interval_vector(a):
    counts = Counter(min((x-y) % 12, (y-x) % 12) for x, y in combinations(a, 2))
    return tuple(counts[k] for k in range(1, 7))


def ps_coordinates(a):
    iv = interval_vector(a)
    return 2*len(a) + 2*iv[1] - 2*iv[3] - 4*iv[5], 2*iv[0] - 2*iv[4]


def orbit(a):
    return {tuple(sorted((x+t) % 12 for x in a)) for t in range(12)}


def m5(a):
    return tuple(sorted(5*x % 12 for x in a))


def verify():
    rows = []
    diatonic = (0, 2, 4, 5, 7, 9, 11)
    diatonic_iv = interval_vector(diatonic)
    diatonic_orbit = orbit(diatonic)
    spectral_maximizers = set()
    energy_minimizers = set()
    for k in range(13):
        reference = tuple(range(k))
        p, q = ps_coordinates(reference)
        maximizers = set()
        tested = 0
        for a in combinations(range(12), k):
            tested += 1
            pa, qa = ps_coordinates(a)
            comparison = sign_sqrt3(p-pa, q-qa)
            assert comparison >= 0, ("Huddling violation", a)
            if comparison == 0:
                maximizers.add(a)
            if k == 7:
                iv = interval_vector(a)
                d = tuple(x-y for x, y in zip(iv, diatonic_iv))
                dd = tuple(sum((j+1-l)*d[l] for l in range(j+1)) for j in range(5))
                assert sum(d) == 0 and min(dd) >= 0, (a, d, dd)
                assert (max(dd) == 0) == (a in diatonic_orbit), (a, dd)
                energy = sum(iv[j]*(6-j)**2 for j in range(6))
                assert energy >= 313, (a, energy)
                if energy == 313:
                    energy_minimizers.add(a)
                if ps_coordinates(m5(a)) == (p, q):
                    spectral_maximizers.add(a)
        assert maximizers == orbit(reference), ("Equality classification", k, maximizers)
        rows.append({"cardinality": k, "subsets_checked": tested,
                     "twice_max_power": {"rational": p, "sqrt3": q},
                     "maximizers": len(maximizers)})
    assert energy_minimizers == spectral_maximizers == diatonic_orbit
    assert m5(diatonic) in orbit(tuple(range(7)))
    return {"universe": "Z12", "total_subsets_checked": sum(r["subsets_checked"] for r in rows),
            "huddling": rows, "diatonic": {"sets_checked": 792, "extremizers": 12,
            "max_power_a5": "7 + 4 sqrt(3)", "min_energy_V0": 313,
            "V0": "(7-k)^2 for distances k=1,...,6",
            "spectral_and_energy_extremizers_equal": True}}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
