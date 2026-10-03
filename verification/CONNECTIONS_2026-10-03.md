# A common symmetry behind complements, hexachords and homometry

Status: checked Lean formalization of classical identities. This document does **not** claim a new mathematical theorem or priority over the literature.

Let `G` be a finite abelian group, let `f : G → ℝ` be even, and put

`W(a,b) = f(b-a)`, `S_f = Σ_{x∈G} f(x)`, and `E_f(A) = ½ Σ_{a,b∈A} W(a,b)`.

The elementary identity `Σ_b f(b-a) = S_f` is the hinge. In particular,

`E_f(G\A) - E_f(A) = (|G|/2 - |A|) S_f`.

This is the short normal form of the general weighted-kernel complement theorem in `ComplementEnergy.lean`. It makes four connections immediate:

1. **Complementary hexachords.** For `G = ℤ/12` and `|A| = 6`, the right-hand side vanishes for every even `f`. This is the all-potentials energy version of the complementary-hexachord interval-vector theorem already present in `Fourier.lean`. The new `PitchClassEnergy.hexachord_energy_eq` checks the energy statement directly in Lean.
2. **Five/seven-note transport.** If `|A| = |B|`, the same correction occurs for both sets, so `E_f(G\A)-E_f(G\B) = E_f(A)-E_f(B)`. Thus minimizers among five-note sets correspond to minimizers among seven-note complements. `TranslationInvariantEnergy.energy_gap_compl` and `minimizer_compl_iff` prove this without another subset census; `ExtremalityConnections.pentatonic_energy_gap` is the earlier twelve-tone specialization for the published energy convention.
3. **Homometry.** Equality of autocorrelations fixes cardinality (at difference zero). The formula `C_{Aᶜ}(t)+2|A|=12+C_A(t)` then shows that complements of homometric sets remain homometric. `ExtremalityConnections.homometric_compl` proves this symbolically. By the earlier `energy_eq_of_homometric`, their complements have equal all-pairs energy for every potential (`energy_compl_eq_of_homometric`). Via the earlier Wiener–Khinchin theorem, this is also a full Fourier-power-spectrum connection.
4. **When the symmetry matters.** The abstract `ComplementEnergy.regular_iff_complement_gaps` proves that constant row sums are exactly the condition for all equal-cardinality energy gaps to survive complementation. Translation-invariant kernels satisfy it automatically; `kernel_symmetric_iff` records that their pair symmetry is exactly evenness of `f`. The finite-group theorem is a sufficient structural explanation, not a claim that all regular kernels are translation invariant.

For the circular-distance potential in the notes, take `f(x)=V(cdist(0,x))`. The Lean theorem `PitchClassEnergy.potential_sum` proves `S_f = V(0)+2Σ_{j=1}^5 V(j)+V(6)`. The published convention `AllPairsEvenness.E` sums only *distinct* unordered pairs, whereas `E_f` includes the diagonal contribution `|A|V(0)/2`. With `V(0)=0`, the normal form reduces to the coefficient `(6-|A|)(2Σ_{j=1}^5 V(j)+V(6))` of `ExtremalityConnections.energy_compl`. `PitchClassEnergy.complement_difference_bridge` now proves directly in Lean that the two complement-difference formulas agree under that normalization. A pointwise equality of the two energy definitions for every set remains an optional representation lemma; the complement theorem used in the note is connected exactly.

New declarations are in `TranslationInvariantEnergy.lean` and `ExtremalityConnections.lean`. Both changed modules compiled with Lean `4.30.0-rc2`, Mathlib `701fb6e9c3b9285968b375d19886bfc5ca134840`, `autoImplicit=false`, `relaxedAutoImplicit=false`; the new declarations report only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or native enumeration. The later [Euler/Huddling continuation](../research/EULER_TO_HUDDLING_2026-10-03.md) replaced the Huddling census by the general structural proof. Diatonic and pentatonic spectral results now use only foundational axioms; the Fourier–energy equivalences retain the energy census.

Mathematical antecedent for the complement/minimizer mechanism: Bushaw, Cody and Leffler, [*Sets of vertices with extremal energy*](https://arxiv.org/abs/2407.18785), especially Theorem 3.5. The hexachord and Fourier/homometry antecedents are cited in the existing Note 1 and Note 5 material. No exhaustive formalization-priority claim is made.
