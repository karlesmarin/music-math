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

`lean/CyclicHuddlingGeometry.lean` closes the geometric selector and the complete
equality analysis. The proof chooses an angular grid cut using the ceiling
function, applies cosine monotonicity to the arc and its complement, and uses
finite exchange. At equality only the two boundary vertices can differ;
exchanging them produces the adjacent arc. Empty and full sets are handled
explicitly. The final results do not assume the selector.

## Completed general theorem

For every `N > 0`, every subset `B` of `ZMod N`, `m = B.card`, and every unit
frequency `k`, the bound is

\[
  |\widehat B(k)| \leq
  \left|\sum_{j=0}^{m-1} \exp(-2\pi i j/N)\right|.
\]

Equality holds exactly when `k B` is a translated consecutive arc. This also
characterizes the maximizers among all subsets of the same cardinality.

| Lean declaration | Certified statement |
|---|---|
| `geometric_selector_with_boundary` | A projection threshold selects an arc, with at most its two boundary vertices tied. |
| `norm_Ahat_one_le_arc` | Sharp frequency-one inequality for every nonzero cyclic order. |
| `norm_Ahat_unit_le_arc` | The same bound for every unit frequency. |
| `norm_Ahat_one_eq_arc_iff` | Equality exactly for translated arcs, including empty and full sets. |
| `norm_Ahat_unit_eq_arc_iff` | Equality exactly when the frequency image is a translated arc. |
| `maximizer_unit_iff` | Equivalent characterization as a global maximum at fixed cardinality. |

All printed axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorry`, added mathematical axiom, `native_decide`,
or finite census in this proof. The precise dependency revision, source hashes,
and compiler results are recorded in `verification/cyclic_huddling_build_report.json`.

## Scope and next connection

For a primitive frequency other than 1, the maximizing pitch set is a pullback
of an arc under multiplication by that frequency. It need not be consecutive
in pitch order. The unit-frequency restriction is essential: in `ZMod 12`,
`B = {0,6}` at frequency `2` has magnitude `2`, exceeding the frequency-one
two-point arc magnitude `sqrt(2 + sqrt(3))`. Repeated character values are
possible because multiplication by `2` is not a permutation of `ZMod 12`.

The proof is complete for the inequality and equality statements above.
Connecting it to the existing twelve-tone radical constants can replace the
old Huddling census; that integration is separate work. The published Note 5
PDF and its existing native proof dependencies have not been revised by this
source-code addition. No universal first-formalization claim is made.
