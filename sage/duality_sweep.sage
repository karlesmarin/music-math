# duality_sweep.sage — when does a CFS-style neo-Riemannian duality exist? (exploration)
# Author: Carles Marin <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)
#
# CFS (the triads) is the case where the T/I group acts SIMPLY TRANSITIVELY (regularly) on a set
# class, so its centralizer in Sym(orbit) is again regular and isomorphic to it (the dual PLR group).
# This sweep catalogues, for EVERY set class in Z/n, whether that duality holds: orbit size, whether
# T/I acts regularly, the order of the centralizer of the T/I-image in Sym(orbit), and whether the
# centralizer is itself transitive/regular. Grounded in Fiore-Noll-Satyendra generalized contextual
# groups; goal = pin down exactly which classes are self-dual and look for anything unnamed.

from itertools import combinations

def run(n):
    def Tk(S, k): return frozenset((x + k) % n for x in S)
    def Ik(S, k): return frozenset((-x + k) % n for x in S)
    def canon(S):
        best = None
        for k in range(n):
            for t in (tuple(sorted(Tk(S, k))), tuple(sorted(Ik(S, k)))):
                if best is None or t < best: best = t
        return best

    seen = {}
    for size in range(1, n):                      # skip empty and full (degenerate)
        for c in combinations(range(n), size):
            S = frozenset(c); cn = canon(S)
            if cn not in seen: seen[cn] = S

    rows = []
    for cn, S in sorted(seen.items(), key=lambda kv: (len(kv[0]), kv[0])):
        orbit = set()
        for k in range(n):
            orbit.add(tuple(sorted(Tk(S, k)))); orbit.add(tuple(sorted(Ik(S, k))))
        O = sorted(orbit); idx = {o: i + 1 for i, o in enumerate(O)}; m = len(O)
        Sg = SymmetricGroup(m)
        gens = []
        for (typ, k) in [('T', 1), ('I', 0)]:     # T_1 and I_0 generate D_n
            perm = []
            for o in O:
                so = frozenset(o)
                img = Tk(so, 1) if typ == 'T' else Ik(so, 0)
                perm.append(idx[tuple(sorted(img))])
            gens.append(Sg(perm))
        G = Sg.subgroup(gens)
        gord = G.order()
        ti_regular = (G.is_transitive() and gord == m and G.stabilizer(1).order() == 1)
        C = Sg._gap_().Centralizer(G._gap_())
        cord = Integer(C.Order())
        c_trans = bool(C.IsTransitive(list(range(1, m + 1))))
        c_regular = c_trans and cord == m
        iso = bool(G._gap_().IsomorphismGroups(C) != gap('fail')) if cord == gord else False
        rows.append((cn, len(cn), m, gord, ti_regular, cord, c_trans, c_regular, iso))

    print("=== Z/%d : %d set classes ===" % (n, len(rows)))
    print("prime_form            |S| orbit |TI|  TIreg  |C|  Ctrans Creg  C~=TI")
    dual = 0
    for (cn, sz, m, gord, tir, cord, ct, cr, iso) in rows:
        if tir and cr and iso: dual += 1
        print("%-21s %2d  %3d  %3d   %-5s %3d  %-5s  %-5s %s" %
              (str(cn), sz, m, gord, tir, cord, ct, cr, iso))
    print(">>> %d / %d set classes admit a CFS-style (regular, self-dual) neo-Riemannian duality" %
          (dual, len(rows)))

run(12)
