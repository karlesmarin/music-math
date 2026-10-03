# General cyclic Huddling: Mathlib overlap and proof status (2026-10-03)

The mathematical Huddling lemma predates this project. Emmanuel Amiot's 2009
*Music Theory Online* article states it for distinct roots of unity in
[Appendix, Lemma 2](https://mtosmt.org/issues/mto.09.15.2/mto.09.15.2.amiot.php).
The possible contribution here is a reusable Lean proof and its connections to
the twelve-tone formalizations, not a claim of a new mathematical inequality.

## Mathlib check

I searched the full local Mathlib source tree at commit
`701fb6e9c3b9285968b375d19886bfc5ca134840` for `huddling`, for
consecutive-root maximization language, and for Fourier-maximization language;
these queries found no statement of the full Huddling inequality or equality
classification. The [current Mathlib Fourier module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/ZMod.html)
defines `ZMod.dft`, and its [additive-character module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.html)
supplies the standard character and primitivity. Mathlib also supplies finite
sum and geometric-series lemmas used by the new file. These checks are bounded
evidence of no located prior formalization; they cannot establish global
absence, and other proof-assistant repositories have not been exhaustively
checked.

## What now compiles

`lean/CyclicHuddling.lean` proves, without `sorry`, the correspondence between
set Fourier sums and Mathlib's DFT, translation invariance of magnitudes,
complement negation at nonzero frequency, cardinality and geometric-series
formulas for arcs, finite exchange inequalities for projected scores, and
the phase-alignment step. It also proves that a unit frequency relabels the
coefficient as a frequency-one coefficient. Its conditional norm theorem shows
that the frequency-one arc bound follows if every unit projection of the roots
admits a translated arc separated from its complement by a score threshold;
the same bound then transfers to every unit frequency.

`lean/CyclicHuddlingGeometry.lean` additionally proves the two cosine comparisons
that separate a circular arc from its complement, and the existence of an
integer grid cut placing any phase in a prescribed angular cell. Connecting
these real-angle lemmas to the finite `ZMod N` selector remains to be done.

## Exact remaining obligation

Prove the geometric selector at frequency `1`, then handle threshold ties to
classify equality. For a **primitive frequency** `k` (equivalently, `k`
coprime to `N`), the maximizing pitch set is a pullback of a consecutive arc
under multiplication by `k`; it need not itself be consecutive in pitch order.
The arc bound is false for arbitrary nonzero `k`: in `ZMod 12` at frequency `2`,
the three consecutive pitches `{0,1,2}` have Fourier magnitude `2`, while
`{0,1,6}` has magnitude `√7`. The latter set repeats one character value,
which is possible because multiplication by `2` is not a permutation of
`ZMod 12`. Thus the primitive-frequency hypothesis is mathematically
necessary for the present consecutive-pitch formulation.

This work is research-stage and is included in the GitHub sources with this
status made explicit. It has not been added to the published Note 5 or presented
as a complete general Huddling formalization.
