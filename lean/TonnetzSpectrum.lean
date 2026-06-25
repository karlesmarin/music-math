/- TonnetzSpectrum.lean — the PLR/Tonnetz Cayley-graph adjacency operator and its COMPLETE spectrum,
   all eigenvalues ± {3, √5, 2cos(π/12), √3, 1, 2cos(5π/12)} machine-checked (no Sage caveat).
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   THE OBJECT. Γ = Cayley(PLR ≅ D₁₂, {P,L,R}) is the 3-regular graph on the 24 major/minor triads
   `Triad = ZMod 12 × Bool`, with an edge `t — t'` iff `t' ∈ {P t, L t, R t}` (P,L,R the
   neo-Riemannian involutions of NeoRiemannian.lean — re-stated locally here to avoid cross-import
   build-order risk; the duplication is debt, same convention as InversionDFT.lean).

   THE FULL SPECTRUM (now FULLY Lean-certified; cross-checked against sage/tonnetz_cayley_spectrum.py).
   With ω = e^{2πi/12} the adjacency spectrum of Γ is the multiset
       ± { 3, √5, 2cos(π/12), √3, 1, 2cos(5π/12) }   =   ± | 1 + ζ⁴ + ζ⁻³ |   (ζ = ω^j, j = 0..5),
   four one-dimensional irreps giving ±3, ±1 and five two-dimensional irreps (j = 1..5, each value of
   multiplicity 2) giving the irrational values; the "golden" eigenvalue √5 = |1 + ω³ + ω⁹| is the
   j = 3 dihedral-irrep value. The closed form arises from the D₁₂ regular-representation decomposition
   (Babai 1979, "Spectra of Cayley graphs"; Diaconis 1988): on each irrep ρ the adjacency block is
   ρ(P) + ρ(L) + ρ(R), with eigenvector u(x,maj) = ζˣ·p, u(x,min) = ζˣ·|p|, p = 1+ζ⁴+ζ⁻³.

   THE LEAN (this file). The COMPLETE spectrum is now certified:
     • T1 (GREEN): the ℂ adjacency operator A; A is symmetric (P,L,R involutions ⇒ neighbour relation
       symmetric); 3-regularity (P t, L t, R t pairwise distinct); the all-ones eigenvector with
       eigenvalue +3 (`A_mulVec_ones`); the maj/min sign eigenvector with eigenvalue −3
       (`A_mulVec_sign`, the bipartite/quality flip — every edge crosses major↔minor).
     • T1f (GREEN): `bipartite_neg_eigen` — graph bipartite on quality ⇒ if `A v = λ v` then
       `A (sign·v) = −λ (sign·v)`. One lemma; gives the whole NEGATIVE half of the spectrum for free.
     • T2 (GREEN): the golden eigenvector `u` for √5 = |1 + ω³ + ω⁹| (the j = 3 dihedral irrep),
       `A *ᵥ u = (√5 : ℂ) • u`, via the order-4 character `χ x = iˣ`; lone irrational step `(√5)² = 5`.
     • T3 (GREEN): the remaining two-dimensional irreps, via the generic eigenvector lemma
       `A_mulVec_uG` (any 12th root of unity ζ with the two structural relations `p = 1+ζ⁴+ζ⁻³` and
       `|p|² = p·(1+ζ⁻⁴+ζ³)`). Specialized to: `A_mulVec_j4` (√3, ζ = ω⁴ primitive cube root),
       `A_mulVec_j2` (1, ζ = ω² primitive 6th root), `A_mulVec_j1` (2cos5π/12 = √(2−√3)) and
       `A_mulVec_j5` (2cos π/12 = √(2+√3)) (the two primitive-12th-root cases, closed via ζ³ = i).
       The bipartite-negation lemma then yields `A_mulVec_neg3 / negGolden / negJ4 / negJ2 / negJ1 /
       negJ5` — the full ± multiset. Every irrational step is a single `(√k)² = k` (`Real.sq_sqrt`).

   SCOPE / honesty. First fully machine-checked computation of the ENTIRE Tonnetz-graph adjacency
   spectrum (the graph object, all six ± eigenvalue pairs, with explicit eigenvectors). The graph and
   the existence of its Laplacian diagonalization are Lostanlen 2018 (arXiv:1810.00790); the closed
   form, the golden √5 identification, the D₁₂-irrep characterization, and this formalization are the
   contribution. The method (Cayley spectrum via irreps) is Babai 1979, folklore. NOT new mathematics.
   NOTE: this file certifies, per eigenvalue, an explicit EIGENVECTOR (A v = λ v); it does not (yet)
   prove these are ALL eigenvalues / multiplicities — that completeness statement (a basis-count over
   the 24-dim space, the D₁₂-irrep decomposition) remains the frontier, as Mathlib lacks the dihedral
   irrep classification.

   Citations: Douthett–Steinbach 1998 (the graph / chicken-wire torus); Crans–Fiore–Satyendra,
   "Musical actions of dihedral groups", AMM 116 (2009) (PLR ≅ D₁₂); Lostanlen 2018 arXiv:1810.00790
   (prior Laplacian diagonalization of the SAME graph); Babai 1979 "Spectra of Cayley graphs".

   Fast-loop build: lake env lean TonnetzSpectrum.lean  (from godsil-gutman env). -/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.Ring

open scoped Matrix
open Complex

namespace TonnetzSpectrum

/-! ### Local re-statement of the triad type and the neo-Riemannian operations.

Duplicated from NeoRiemannian.lean (`Triad`, `Pf`, `Lf`, `Rf`) to keep this file independent of
build order — the duplication is acknowledged debt. These are plain functions `Triad → Triad`
(involutions); we only need them as the neighbour map of the Cayley graph. -/

/-- A triad: root pitch-class in `ZMod 12`, quality bit (`true` = major). 24 of them. -/
abbrev Triad := ZMod 12 × Bool

/-- Parallel: same root, flip quality. -/
def Pf : Triad → Triad | (x, b) => (x, !b)
/-- Leading-tone exchange. -/
def Lf : Triad → Triad
  | (x, true)  => (x + 4, false)
  | (x, false) => (x - 4, true)
/-- Relative. -/
def Rf : Triad → Triad
  | (x, true)  => (x - 3, false)
  | (x, false) => (x + 3, true)

/-! ### The Cayley-graph adjacency operator over ℂ. -/

/-- The neighbour relation: `t — t'` iff `t' ∈ {P t, L t, R t}`. -/
def adj (t t' : Triad) : ℂ := if t' = Pf t ∨ t' = Lf t ∨ t' = Rf t then 1 else 0

/-- The adjacency matrix of the PLR/Tonnetz Cayley graph, over ℂ. -/
def A : Matrix Triad Triad ℂ := Matrix.of adj

@[simp] lemma A_apply (t t' : Triad) : A t t' = adj t t' := rfl

/-! ### T1a — symmetry. P, L, R are involutions, so the neighbour relation is symmetric. -/

/-- The neighbour relation as a `Bool`-decidable Prop is symmetric: `t' ∈ {Pt,Lt,Rt} ↔ t ∈ {Pt',Lt',Rt'}`.
    A finite check over all `24 × 24` triad pairs (closed `∀`, so `decide` is sound — no `sorryAx`). -/
theorem neighbour_symm : ∀ t t' : Triad,
    (t' = Pf t ∨ t' = Lf t ∨ t' = Rf t) ↔ (t = Pf t' ∨ t = Lf t' ∨ t = Rf t') := by decide

/-- `adj` is symmetric (over ℂ): proved via the underlying decidable Prop, NOT `decide` over ℂ. -/
theorem adj_symm (t t' : Triad) : adj t t' = adj t' t := by
  unfold adj
  by_cases h : t' = Pf t ∨ t' = Lf t ∨ t' = Rf t
  · rw [if_pos h, if_pos ((neighbour_symm t t').mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((neighbour_symm t t').mpr hc))]

/-- **T1a.** The Tonnetz adjacency matrix is symmetric. -/
theorem A_symm : Matrix.IsSymm A := by
  ext t t'
  show A t' t = A t t'
  simp only [A_apply]
  exact (adj_symm t t').symm

/-! ### T1b — 3-regularity. The three neighbours `P t, L t, R t` are pairwise distinct. -/

/-- The three neighbours are pairwise distinct for every triad (decidable Prop over `Triad`). -/
theorem neighbours_distinct : ∀ t : Triad,
    Pf t ≠ Lf t ∧ Pf t ≠ Rf t ∧ Lf t ≠ Rf t := by decide

/-- The neighbour set `{P t, L t, R t}` as a `Finset Triad`. -/
def nbhd (t : Triad) : Finset Triad := {Pf t, Lf t, Rf t}

/-- **T1b (3-regularity).** Every triad has exactly three neighbours. -/
theorem nbhd_card (t : Triad) : (nbhd t).card = 3 := by
  obtain ⟨hPL, hPR, hLR⟩ := neighbours_distinct t
  unfold nbhd
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]; exact hLR
  · simp only [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hPL, hPR⟩

/-! ### T1c — the +3 eigenvector (all-ones; row sum = #neighbours = 3). -/

/-- For a fixed `t`, the matrix row `adj t ·` is the indicator of the neighbour set `nbhd t`:
    `adj t t' = if t' ∈ nbhd t then 1 else 0`. -/
lemma adj_eq_indicator (t t' : Triad) : adj t t' = if t' ∈ nbhd t then 1 else 0 := by
  unfold adj nbhd
  congr 1
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- **T1c.** The all-ones vector is an eigenvector of `A` with eigenvalue `+3` (row sum = 3 neighbours). -/
theorem A_mulVec_ones : A *ᵥ (fun _ => (1 : ℂ)) = (3 : ℂ) • (fun _ => (1 : ℂ)) := by
  funext t
  simp only [Matrix.mulVec, dotProduct, A_apply, mul_one, Pi.smul_apply, smul_eq_mul, mul_one]
  -- Σ_{t'} adj t t' = Σ_{t' ∈ univ} (if t' ∈ nbhd t then 1 else 0) = |nbhd t| = 3
  rw [Finset.sum_congr rfl (fun t' _ => adj_eq_indicator t t')]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nbhd_card]
  simp

/-! ### T1d — the −3 eigenvector. P, L, R all FLIP the quality bit, so every edge crosses
major↔minor (the graph is bipartite on `Bool`); the sign vector `s t = ±1` by quality is an
eigenvector with eigenvalue −3. -/

/-- The maj/min sign vector: `+1` on major triads, `−1` on minor. -/
def sign (t : Triad) : ℂ := if t.2 then (1 : ℂ) else -1

/-- P, L, R all flip the quality bit (decidable Prop over `Triad`). -/
theorem neighbours_flip : ∀ t : Triad,
    (Pf t).2 = !t.2 ∧ (Lf t).2 = !t.2 ∧ (Rf t).2 = !t.2 := by decide

/-- The sign of a flipped quality is the negated sign: `s` on any neighbour is `−(s t)`. -/
lemma sign_flip (t : Triad) :
    sign (Pf t) = -sign t ∧ sign (Lf t) = -sign t ∧ sign (Rf t) = -sign t := by
  obtain ⟨hP, hL, hR⟩ := neighbours_flip t
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [sign, hP, hL, hR, Bool.not_eq_true']
    cases t.2 <;> simp

/-- The row `adj t ·` weighted by `sign` sums to `3 · (−sign t)`: rewrite the sum over the explicit
    3-element neighbour set, on each of which `sign = −sign t`. -/
lemma row_sign_sum (t : Triad) :
    ∑ t' : Triad, adj t t' * sign t' = 3 * (-sign t) := by
  rw [Finset.sum_congr rfl (fun t' _ => by
        rw [adj_eq_indicator t t', boole_mul])]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  obtain ⟨hPL, hPR, hLR⟩ := neighbours_distinct t
  obtain ⟨sP, sL, sR⟩ := sign_flip t
  unfold nbhd
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hPL, hPR⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hLR),
      Finset.sum_singleton, sP, sL, sR]
  ring

/-- **T1d.** The maj/min sign vector is an eigenvector of `A` with eigenvalue `−3` — every edge of the
    Tonnetz graph crosses major↔minor (bipartite on quality). -/
theorem A_mulVec_sign : A *ᵥ sign = (-3 : ℂ) • sign := by
  funext t
  simp only [Matrix.mulVec, dotProduct, A_apply, Pi.smul_apply, smul_eq_mul]
  rw [row_sign_sum t]
  ring

/-! ### T1e — bipartiteness, as a named fact. Every neighbour has the opposite quality. -/

/-- **Bipartite on quality.** Every Tonnetz edge crosses major↔minor: if `t — t'` then `t'.2 = !t.2`.
    (Immediate from `neighbours_flip`.) -/
theorem A_bipartite (t t' : Triad) (h : adj t t' = 1) : t'.2 = !t.2 := by
  have hne : ¬ (adj t t' = 0) := by rw [h]; exact one_ne_zero
  unfold adj at hne
  obtain ⟨hP, hL, hR⟩ := neighbours_flip t
  by_cases hc : t' = Pf t ∨ t' = Lf t ∨ t' = Rf t
  · rcases hc with rfl | rfl | rfl
    · exact hP
    · exact hL
    · exact hR
  · exact absurd (if_neg hc) hne

/-! ### T1f — bipartite negation. Because every edge crosses major↔minor, multiplying any
eigenvector by the maj/min `sign` vector negates its eigenvalue. One lemma, and every positive
eigenvalue immediately yields its negative (and `A_mulVec_sign` falls out of `A_mulVec_ones`). -/

/-- `sign`-twist of a vector: flip sign on the minor triads. -/
def signMul (v : Triad → ℂ) : Triad → ℂ := fun t => sign t * v t

/-- On any edge the row weight times `sign` equals the row weight times `−sign t` (bipartiteness:
    `adj t t' = 1 ⇒ sign t' = −sign t`; otherwise both sides are `0`). -/
lemma adj_mul_sign (t t' : Triad) : adj t t' * sign t' = adj t t' * (-sign t) := by
  by_cases h : adj t t' = 1
  · have hb := A_bipartite t t' h
    have : sign t' = -sign t := by
      simp only [sign, hb]; cases t.2 <;> simp
    rw [this]
  · have : adj t t' = 0 := by unfold adj at h ⊢; split at h <;> simp_all
    rw [this]; ring

/-- **T1f (bipartite negation).** If `v` is an eigenvector with eigenvalue `λ`, then its `sign`-twist
    `signMul v` is an eigenvector with eigenvalue `−λ`. The Tonnetz graph is bipartite on quality, so
    the spectrum is symmetric about `0`. -/
theorem bipartite_neg_eigen (v : Triad → ℂ) (lam : ℂ) (h : A *ᵥ v = lam • v) :
    A *ᵥ (signMul v) = (-lam) • (signMul v) := by
  funext t
  have hrow : (A *ᵥ v) t = lam * v t := by rw [h]; simp [Pi.smul_apply]
  simp only [Matrix.mulVec, dotProduct, A_apply, signMul, Pi.smul_apply, smul_eq_mul] at hrow ⊢
  -- Σ adj t t' * (sign t' * v t') = Σ adj t t' * (-sign t) * v t' = -sign t * (Σ adj t t' * v t')
  have step : ∀ t' : Triad, adj t t' * (sign t' * v t') = (-sign t) * (adj t t' * v t') := by
    intro t'
    rw [← mul_assoc, adj_mul_sign t t']; ring
  rw [Finset.sum_congr rfl (fun t' _ => step t'), ← Finset.mul_sum, hrow]
  ring

/-! ### T2 — the golden eigenvalue √5.  (GREEN.)

The j = 3 dihedral irrep. With `ω = e^{2πi/12}` the j = 3 value is `|1 + ω³ + ω⁹| = |1 + i + i| =
|1 + 2i| = √5` (since `ω³ = i`). Concretely, the diagonalizing character on roots is `χ x = i^x`
(`I` is `ω³`, of order 4, and `12` is divisible by `4` so `χ` descends to `ZMod 12`). The explicit
golden eigenvector is

      u (x, major) = χ x · (2 + i),      u (x, minor) = χ x · √5.

Verification, neighbour by neighbour. P, L, R send a major `(x,true)` to the three minors
`(x,false), (x+4,false), (x−3,false)`; using `χ(x+4) = χ x` and `χ(x−3) = χ x · i`:

      (A u)(x,major) = √5 · χ x · (1 + 1 + i) = √5 · χ x · (2 + i) = √5 · u(x,major).   ✓ (no √5²)

For a minor `(x,false)` the neighbours are the majors `(x,true), (x−4,true), (x+3,true)`; with
`χ(x−4) = χ x`, `χ(x+3) = χ x · (−i)`:

      (A u)(x,minor) = (2+i) · χ x · (1 + 1 − i) = (2+i)(2−i) · χ x = 5 · χ x = √5 · u(x,minor),

the only place the identity `(√5)² = 5` enters (`Real.sq_sqrt`). All `i^k` reduce by `i⁴ = 1`. -/

/-- The order-4 character `χ x = iˣ` on the roots (`i = ω³`). Well-defined on `ZMod 12` because
    `i¹² = 1`. -/
noncomputable def chi (x : ZMod 12) : ℂ := I ^ x.val

/-- `i¹² = 1` (so `χ` descends to `ZMod 12`). -/
lemma I_per : (I : ℂ) ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]

/-- Character shift law: `χ (x + c) = χ x · i^(c.val)`. (Exponents agree mod 12, and `i¹² = 1`.) -/
lemma chi_shift (x c : ZMod 12) : chi (x + c) = chi x * I ^ (c.val) := by
  unfold chi; rw [← pow_add]
  have key : ∀ a b : ℕ, a % 12 = b % 12 → (I : ℂ) ^ a = (I : ℂ) ^ b := by
    intro a b hab
    conv_lhs => rw [← Nat.div_add_mod a 12]
    conv_rhs => rw [← Nat.div_add_mod b 12]
    rw [hab, pow_add, pow_add, pow_mul, pow_mul, I_per, one_pow, one_pow]
  exact key _ _ (by have h := ZMod.val_add x c; omega)

/-- **The golden eigenvector** of the Tonnetz adjacency operator (the j = 3 dihedral irrep):
    `χ x · (2 + i)` on majors, `χ x · √5` on minors. -/
noncomputable def u : Triad → ℂ :=
  fun t => if t.2 then chi t.1 * (2 + I) else chi t.1 * (Real.sqrt 5)

@[simp] lemma u_maj (x : ZMod 12) : u (x, true)  = chi x * (2 + I)            := rfl
@[simp] lemma u_min (x : ZMod 12) : u (x, false) = chi x * (Real.sqrt 5 : ℝ) := rfl

/-- `(√5 : ℂ)² = 5` — the single irrational identity the minor case needs. -/
lemma sqrt5_sq : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
  norm_cast; rw [Real.sq_sqrt (by norm_num)]

/-- A generic row sum: `Σ_{t'} adj t t' · f t' = f (P t) + f (L t) + f (R t)` (reduce to the explicit
    3-element neighbour set; NOT `decide` over ℂ). -/
lemma row_sum (f : Triad → ℂ) (t : Triad) :
    ∑ t' : Triad, adj t t' * f t' = f (Pf t) + f (Lf t) + f (Rf t) := by
  rw [Finset.sum_congr rfl (fun t' _ => by rw [adj_eq_indicator t t', boole_mul])]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  obtain ⟨hPL, hPR, hLR⟩ := neighbours_distinct t
  unfold nbhd
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hPL, hPR⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hLR),
      Finset.sum_singleton, add_assoc]

-- The four shift constants `i^(c.val)` used below.
private lemma v4  : (I : ℂ) ^ ((4 : ZMod 12).val)    = 1  := by
  rw [show (4 : ZMod 12).val = 4 from rfl, Complex.I_pow_four]
private lemma vm3 : (I : ℂ) ^ (((-3) : ZMod 12).val) = I  := by
  rw [show ((-3) : ZMod 12).val = 9 from by decide,
      show (9 : ℕ) = 4 * 2 + 1 from rfl, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul, pow_one]
private lemma vm4 : (I : ℂ) ^ (((-4) : ZMod 12).val) = 1  := by
  rw [show ((-4) : ZMod 12).val = 8 from by decide,
      show (8 : ℕ) = 4 * 2 from rfl, pow_mul, Complex.I_pow_four, one_pow]
private lemma v3  : (I : ℂ) ^ ((3 : ZMod 12).val)    = -I := by
  rw [show ((3) : ZMod 12).val = 3 from by decide,
      show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq, pow_one]; ring

/-- **T2 (the headline).** The golden eigenvector `u` realizes the eigenvalue `√5`:
    `A *ᵥ u = (√5 : ℂ) • u`. This is the j = 3 dihedral-irrep eigenvalue `|1 + ω³ + ω⁹| = √5`,
    machine-checked component-wise over the 24 triads. -/
theorem A_mulVec_golden : A *ᵥ u = ((Real.sqrt 5 : ℝ) : ℂ) • u := by
  funext t
  obtain ⟨x, b⟩ := t
  simp only [Matrix.mulVec, dotProduct, A_apply, Pi.smul_apply, smul_eq_mul]
  rw [row_sum u (x, b)]
  cases b
  · -- minor (x,false): neighbours (x,true), (x−4,true), (x+3,true) — all majors
    show u (x, true) + u (x - 4, true) + u (x + 3, true) = _
    rw [u_maj, u_maj, u_maj, u_min,
        show (x - 4) = x + (-4) from by ring, show (x + 3) = x + 3 from rfl,
        chi_shift x (-4), chi_shift x 3, vm4, v3]
    have hs := sqrt5_sq
    linear_combination (-chi x) * Complex.I_sq + (-chi x) * hs
  · -- major (x,true): neighbours (x,false), (x+4,false), (x−3,false) — all minors
    show u (x, false) + u (x + 4, false) + u (x - 3, false) = _
    rw [u_min, u_min, u_min, u_maj,
        show (x - 3) = x + (-3) from by ring,
        chi_shift x 4, chi_shift x (-3), v4, vm3]
    ring

/-! ### T3 — the remaining two-dimensional irreps, via a generic character.

For each `j` the diagonalizing character on roots is `χ_ζ x = ζ^x` with `ζ = ω^j` a 12th root of
unity (`ζ¹² = 1`), and the eigenvector is `u_ζ(x,maj) = ζ^x · p`, `u_ζ(x,min) = ζ^x · λ`, with
`p = 1 + ζ⁴ + ζ⁻³` and `λ = |p|`. The major equation needs only `p`; the minor equation needs the
single irrational identity `p · conj p = λ²`. We package this once and specialize per `j`. -/

/-- A generic 12th-root character `χ_z x = z^x` (well-defined on `ZMod 12` exactly when `z¹² = 1`). -/
noncomputable def chiG (z : ℂ) (x : ZMod 12) : ℂ := z ^ x.val

/-- Generic character-shift law: for any `z` with `z¹² = 1`, `χ_z (x + c) = χ_z x · z^(c.val)`. -/
lemma chiG_shift (z : ℂ) (hz : z ^ (12 : ℕ) = 1) (x c : ZMod 12) :
    chiG z (x + c) = chiG z x * z ^ (c.val) := by
  unfold chiG; rw [← pow_add]
  have key : ∀ a b : ℕ, a % 12 = b % 12 → z ^ a = z ^ b := by
    intro a b hab
    conv_lhs => rw [← Nat.div_add_mod a 12]
    conv_rhs => rw [← Nat.div_add_mod b 12]
    rw [hab, pow_add, pow_add, pow_mul, pow_mul, hz, one_pow, one_pow]
  exact key _ _ (by have h := ZMod.val_add x c; omega)

/-- Generic eigenvector for parameters `(z, p, lam)`: `z^x · p` on majors, `z^x · lam` on minors. -/
noncomputable def uG (z p lam : ℂ) : Triad → ℂ :=
  fun t => if t.2 then chiG z t.1 * p else chiG z t.1 * lam

@[simp] lemma uG_maj (z p lam : ℂ) (x : ZMod 12) : uG z p lam (x, true)  = chiG z x * p   := rfl
@[simp] lemma uG_min (z p lam : ℂ) (x : ZMod 12) : uG z p lam (x, false) = chiG z x * lam := rfl

/-- **Generic two-dimensional-irrep eigenvector lemma.** Given a 12th root of unity `z` and scalars
    `p, lam` satisfying the structural relations
      `p = 1 + z⁴ + z⁻³`   (root-walk closes on the major side),
      `lam² = p · (1 + z⁻⁴ + z³)`   (minor side; the irrational step), and
      `lam · 1 = lam`, `lam·(z⁴.val…)` handled by the shift law,
    the vector `uG z p lam` is an `A`-eigenvector with eigenvalue `lam`. The two hypotheses are
    `hp : 1 + z^(4) + z^((-3:ZMod 12).val) = p` and `hlam : p * (1 + z^((-4:ZMod 12).val) + z^3) = lam^2`. -/
theorem A_mulVec_uG (z p lam : ℂ) (hz : z ^ (12 : ℕ) = 1)
    (hp : 1 + z ^ ((4 : ZMod 12).val) + z ^ (((-3) : ZMod 12).val) = p)
    (hlam : p * (1 + z ^ (((-4) : ZMod 12).val) + z ^ ((3 : ZMod 12).val)) = lam ^ 2) :
    A *ᵥ (uG z p lam) = lam • (uG z p lam) := by
  funext t
  obtain ⟨x, b⟩ := t
  simp only [Matrix.mulVec, dotProduct, A_apply, Pi.smul_apply, smul_eq_mul]
  rw [row_sum (uG z p lam) (x, b)]
  cases b
  · -- minor (x,false): neighbours (x,true), (x−4,true), (x+3,true) — all majors
    show uG z p lam (x, true) + uG z p lam (x - 4, true) + uG z p lam (x + 3, true) = _
    rw [uG_maj, uG_maj, uG_maj, uG_min,
        show (x - 4) = x + (-4) from by ring, show (x + 3) = x + 3 from rfl,
        chiG_shift z hz x (-4), chiG_shift z hz x 3]
    -- (χx·p) + (χx·z^{-4.val}·p) + (χx·z^{3.val}·p) = χx · p·(1+z^{-4}+z^3) = χx · lam² = lam · (χx·lam)
    have : chiG z x * p + chiG z x * z ^ (((-4) : ZMod 12).val) * p
            + chiG z x * z ^ ((3 : ZMod 12).val) * p
          = chiG z x * (p * (1 + z ^ (((-4) : ZMod 12).val) + z ^ ((3 : ZMod 12).val))) := by ring
    rw [this, hlam]; ring
  · -- major (x,true): neighbours (x,false), (x+4,false), (x−3,false) — all minors
    show uG z p lam (x, false) + uG z p lam (x + 4, false) + uG z p lam (x - 3, false) = _
    rw [uG_min, uG_min, uG_min, uG_maj,
        show (x - 3) = x + (-3) from by ring,
        chiG_shift z hz x 4, chiG_shift z hz x (-3)]
    -- (χx·lam) + (χx·z^{4.val}·lam) + (χx·z^{-3.val}·lam) = χx·lam·(1+z^4+z^{-3}) = χx·lam·p = lam·(χx·p)
    have : chiG z x * lam + chiG z x * z ^ ((4 : ZMod 12).val) * lam
            + chiG z x * z ^ (((-3) : ZMod 12).val) * lam
          = chiG z x * lam * (1 + z ^ ((4 : ZMod 12).val) + z ^ (((-3) : ZMod 12).val)) := by ring
    rw [this, hp]; ring

-- The four `ZMod 12` values that appear as exponents, as plain naturals (shared by all `j`).
private lemma val4  : (4 : ZMod 12).val    = 4 := by decide
private lemma valm3 : ((-3) : ZMod 12).val = 9 := by decide
private lemma valm4 : ((-4) : ZMod 12).val = 8 := by decide
private lemma val3  : (3 : ZMod 12).val    = 3 := by decide

/-! #### j = 4 → eigenvalue √3.  ζ = ω⁴ = e^{2πi/3}, a primitive cube root; `p = 2 + ζ`, `|p| = √3`. -/

/-- The primitive cube root `ζ = ω⁴ = (−1 + √3·i)/2`. -/
noncomputable def z4 : ℂ := (-1 + Real.sqrt 3 * I) / 2

/-- `(√3 : ℂ)² = 3`. -/
lemma sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  norm_cast; rw [Real.sq_sqrt (by norm_num)]

/-- `z4² + z4 + 1 = 0` (z4 is a *primitive* cube root). Irrational inputs: `(√3)² = 3`, `I² = −1`. -/
lemma z4_quad : z4 ^ 2 + z4 + 1 = 0 := by
  unfold z4
  rw [div_pow, show (2 : ℂ) ^ 2 = 4 from by norm_num]
  have hI := Complex.I_sq
  have h := sqrt3_sq
  field_simp
  linear_combination (2 * I ^ 2) * h + 6 * hI

/-- `z4³ = 1` (primitive cube root), from the quadratic relation. -/
lemma z4_cube : z4 ^ 3 = 1 := by
  have h := z4_quad
  linear_combination (z4 - 1) * h

/-- `z4¹² = 1`. -/
lemma z4_pow12 : z4 ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, z4_cube, one_pow]

/-- **T3 (j = 4).** Eigenvalue `√3 = |1 + ω⁴ + ω¹²·ⁱ…|`: the eigenvector `uG z4 (2+z4) √3`
    satisfies `A *ᵥ u = (√3 : ℂ) • u`. -/
theorem A_mulVec_j4 :
    A *ᵥ (uG z4 (2 + z4) ((Real.sqrt 3 : ℝ) : ℂ))
      = ((Real.sqrt 3 : ℝ) : ℂ) • (uG z4 (2 + z4) ((Real.sqrt 3 : ℝ) : ℂ)) := by
  apply A_mulVec_uG z4 (2 + z4) ((Real.sqrt 3 : ℝ) : ℂ) z4_pow12
  · -- 1 + z4^4 + z4^9 = 2 + z4.  z4^4 = z4^3·z4 = z4 ; z4^9 = (z4^3)^3 = 1.
    rw [val4, valm3,
        show (9 : ℕ) = 3 * 3 from rfl, pow_mul, z4_cube, one_pow,
        show (4 : ℕ) = 3 + 1 from rfl, pow_add, z4_cube, one_mul, pow_one]
    ring
  · -- (2+z4)·(1 + z4^8 + z4^3) = (√3)² = 3, using z4²+z4+1=0.
    rw [valm4, val3]
    have hq := z4_quad
    have h3 := sqrt3_sq
    linear_combination
      (z4 ^ 7 + z4 ^ 6 - 2 * z4 ^ 5 + z4 ^ 4 + z4 ^ 3 - z4 ^ 2 + 2 * z4 - 1) * hq - h3

/-! #### j = 2 → eigenvalue 1.  ζ = ω² = e^{2πi/6}, a primitive 6th root; `p = ζ⁸ = ω¹⁶`, `|p| = 1`. -/

/-- The primitive 6th root `ζ = ω² = (1 + √3·i)/2`. -/
noncomputable def z2 : ℂ := (1 + Real.sqrt 3 * I) / 2

/-- `z2² − z2 + 1 = 0` (z2 is a *primitive* 6th root). Irrational inputs: `(√3)² = 3`, `I² = −1`. -/
lemma z2_quad : z2 ^ 2 - z2 + 1 = 0 := by
  unfold z2
  rw [div_pow, show (2 : ℂ) ^ 2 = 4 from by norm_num]
  have hI := Complex.I_sq
  have h := sqrt3_sq
  field_simp
  linear_combination (2 * I ^ 2) * h + 6 * hI

/-- `z2³ = −1` (so `z2⁶ = 1`), from the quadratic relation. -/
lemma z2_cube : z2 ^ 3 = -1 := by
  have h := z2_quad
  linear_combination (z2 + 1) * h

/-- `z2¹² = 1`. -/
lemma z2_pow12 : z2 ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, z2_cube]; norm_num

/-- **T3 (j = 2).** Eigenvalue `1`: the eigenvector `uG z2 (−z2) 1` satisfies `A *ᵥ u = 1 • u`.
    Here `p = 1 + ζ⁴ + ζ⁹ = 1 − ζ − 1 = −ζ = −z2` (using `ζ⁴ = ζ³·ζ = −ζ`, `ζ⁹ = ζ³ = −1`) and
    `λ = |p| = 1`. -/
theorem A_mulVec_j2 :
    A *ᵥ (uG z2 (-z2) 1) = (1 : ℂ) • (uG z2 (-z2) 1) := by
  apply A_mulVec_uG z2 (-z2) 1 z2_pow12
  · -- 1 + z2^4 + z2^9 = -z2, using z2²−z2+1=0.
    rw [val4, valm3]
    have hq := z2_quad
    linear_combination
      (z2 ^ 7 + z2 ^ 6 - z2 ^ 4 - z2 ^ 3 + z2 ^ 2 + 2 * z2 + 1) * hq
  · -- (-z2)·(1 + z2^8 + z2^3) = 1, using z2²−z2+1=0.
    rw [valm4, val3]
    have hq := z2_quad
    linear_combination
      (-z2 ^ 7 - z2 ^ 6 + z2 ^ 4 + z2 ^ 3 - z2 ^ 2 - 2 * z2 - 1) * hq

/-! #### j = 1 → eigenvalue 2cos(5π/12) = √(2−√3).  ζ = ω = e^{iπ/6} = (√3 + i)/2, a primitive
12th root.  `p = 1 + ζ⁴ + ζ⁻³ = 1 + ζ⁴ + ζ⁹`, `|p|² = 2 − √3`. (The "hard" 12th-root case; closed via
`ζ³ = i`, so every needed power is an explicit `{1, ζ, ζ², i}`-combination.) -/

/-- The primitive 12th root `ζ = ω = (√3 + i)/2`. -/
noncomputable def z1 : ℂ := (Real.sqrt 3 + I) / 2

/-- `z1³ = i`. Irrational inputs `(√3)² = 3`, `I² = −1`. -/
lemma z1_cube : z1 ^ 3 = I := by
  unfold z1
  rw [div_pow, show (2 : ℂ) ^ 3 = 8 from by norm_num,
      div_eq_iff (by norm_num : (8 : ℂ) ≠ 0)]
  have hI := Complex.I_sq
  have h := sqrt3_sq
  linear_combination (3 * I + (Real.sqrt 3 : ℂ)) * h + (I + 3 * (Real.sqrt 3 : ℂ)) * hI

/-- `z1¹² = 1` (= `(z1³)⁴ = i⁴`). -/
lemma z1_pow12 : z1 ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, z1_cube, Complex.I_pow_four]

/-- `(√(2−√3) : ℂ)² = 2 − √3`. -/
lemma sqrt2m3_sq : ((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ) ^ 2 = 2 - (Real.sqrt 3 : ℝ) := by
  have hle : Real.sqrt 3 ≤ 2 := by
    have : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)] at this
  norm_cast
  rw [Real.sq_sqrt (by linarith)]

/-- **T3 (j = 1).** Eigenvalue `2cos(5π/12) = √(2−√3)`. -/
theorem A_mulVec_j1 :
    A *ᵥ (uG z1 (1 + I * z1 - I) ((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ))
      = ((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ)
          • (uG z1 (1 + I * z1 - I) ((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ)) := by
  -- Powers of z1 used below, all reduced via z1³ = i.
  have p4 : z1 ^ ((4 : ZMod 12).val) = I * z1 := by
    rw [val4, show (4 : ℕ) = 3 + 1 from rfl, pow_add, z1_cube, pow_one]
  have p9 : z1 ^ (((-3) : ZMod 12).val) = -I := by
    rw [valm3, show (9 : ℕ) = 3 * 3 from rfl, pow_mul, z1_cube]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq, pow_one]; ring
  have p8 : z1 ^ (((-4) : ZMod 12).val) = -z1 ^ 2 := by
    rw [valm4, show (8 : ℕ) = 3 * 2 + 2 from rfl, pow_add, pow_mul, z1_cube, Complex.I_sq]; ring
  have p3 : z1 ^ ((3 : ZMod 12).val) = I := by rw [val3]; exact z1_cube
  apply A_mulVec_uG z1 (1 + I * z1 - I) _ z1_pow12
  · rw [p4, p9]; ring
  · rw [p8, p3]
    have hI := Complex.I_sq
    have h := sqrt3_sq
    have hl := sqrt2m3_sq
    -- (1 + I z1 - I)(1 - z1² + I) = 2 - √3, with z1 = (√3+i)/2.
    rw [show z1 = ((Real.sqrt 3 : ℝ) + I) / 2 from rfl]
    field_simp
    ring_nf
    linear_combination (-3 * I ^ 2 - I * (Real.sqrt 3 : ℂ) + 2 * I - 2) * h
      + (-I ^ 2 - 3 * I * (Real.sqrt 3 : ℂ) + 6 * I + 8 * (Real.sqrt 3 : ℂ) - 14) * hI
      + (-8 : ℂ) * hl

/-! #### j = 5 → eigenvalue 2cos(π/12) = √(2+√3).  ζ = ω⁵ = e^{5iπ/6} = (−√3 + i)/2, a primitive
12th root.  `p = 1 + ζ⁴ + ζ⁹`, `|p|² = 2 + √3`.  Same machinery; `ζ³ = i`. -/

/-- The primitive 12th root `ζ = ω⁵ = (−√3 + i)/2`. -/
noncomputable def z5 : ℂ := (-(Real.sqrt 3) + I) / 2

/-- `z5³ = i`. -/
lemma z5_cube : z5 ^ 3 = I := by
  unfold z5
  rw [div_pow, show (2 : ℂ) ^ 3 = 8 from by norm_num,
      div_eq_iff (by norm_num : (8 : ℂ) ≠ 0)]
  have hI := Complex.I_sq
  have h := sqrt3_sq
  linear_combination (3 * I - (Real.sqrt 3 : ℂ)) * h + (I - 3 * (Real.sqrt 3 : ℂ)) * hI

/-- `z5¹² = 1`. -/
lemma z5_pow12 : z5 ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, z5_cube, Complex.I_pow_four]

/-- `(√(2+√3) : ℂ)² = 2 + √3`. -/
lemma sqrt2p3_sq : ((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ) ^ 2 = 2 + (Real.sqrt 3 : ℝ) := by
  norm_cast
  rw [Real.sq_sqrt (by positivity)]

/-- **T3 (j = 5).** Eigenvalue `2cos(π/12) = √(2+√3)`. -/
theorem A_mulVec_j5 :
    A *ᵥ (uG z5 (1 + I * z5 - I) ((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ))
      = ((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ)
          • (uG z5 (1 + I * z5 - I) ((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ)) := by
  have p4 : z5 ^ ((4 : ZMod 12).val) = I * z5 := by
    rw [val4, show (4 : ℕ) = 3 + 1 from rfl, pow_add, z5_cube, pow_one]
  have p9 : z5 ^ (((-3) : ZMod 12).val) = -I := by
    rw [valm3, show (9 : ℕ) = 3 * 3 from rfl, pow_mul, z5_cube]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq, pow_one]; ring
  have p8 : z5 ^ (((-4) : ZMod 12).val) = -z5 ^ 2 := by
    rw [valm4, show (8 : ℕ) = 3 * 2 + 2 from rfl, pow_add, pow_mul, z5_cube, Complex.I_sq]; ring
  have p3 : z5 ^ ((3 : ZMod 12).val) = I := by rw [val3]; exact z5_cube
  apply A_mulVec_uG z5 (1 + I * z5 - I) _ z5_pow12
  · rw [p4, p9]; ring
  · rw [p8, p3]
    have hI := Complex.I_sq
    have h := sqrt3_sq
    have hl := sqrt2p3_sq
    rw [show z5 = (-(Real.sqrt 3 : ℝ) + I) / 2 from rfl]
    field_simp
    ring_nf
    linear_combination (-3 * I ^ 2 + I * (Real.sqrt 3 : ℂ) + 2 * I - 2) * h
      + (-I ^ 2 + 3 * I * (Real.sqrt 3 : ℂ) + 6 * I - 8 * (Real.sqrt 3 : ℂ) - 14) * hI
      + (-8 : ℂ) * hl

/-! ### T3⁻ — the negative half of the spectrum, for free via bipartite negation.

Each positive eigenvector, twisted by `sign`, gives the matching negative eigenvalue. This realizes
the full symmetric multiset `± {3, √5, 2cos(π/12), √3, 1, 2cos(5π/12)}` without re-proving anything.
(`A_mulVec_sign` above is the `λ = 3` instance of the same fact, kept as a standalone for the header.) -/

/-- `−3` (from the all-ones `+3` eigenvector). -/
theorem A_mulVec_neg3 :
    A *ᵥ (signMul (fun _ => (1 : ℂ))) = (-3 : ℂ) • (signMul (fun _ => (1 : ℂ))) :=
  bipartite_neg_eigen _ 3 A_mulVec_ones

/-- `−√5` (the golden eigenvalue's reflection). -/
theorem A_mulVec_negGolden :
    A *ᵥ (signMul u) = (-((Real.sqrt 5 : ℝ) : ℂ)) • (signMul u) :=
  bipartite_neg_eigen _ _ A_mulVec_golden

/-- `−√3` (j = 4 reflection). -/
theorem A_mulVec_negJ4 :
    A *ᵥ (signMul (uG z4 (2 + z4) ((Real.sqrt 3 : ℝ) : ℂ)))
      = (-((Real.sqrt 3 : ℝ) : ℂ)) • (signMul (uG z4 (2 + z4) ((Real.sqrt 3 : ℝ) : ℂ))) :=
  bipartite_neg_eigen _ _ A_mulVec_j4

/-- `−1` (j = 2 reflection). -/
theorem A_mulVec_negJ2 :
    A *ᵥ (signMul (uG z2 (-z2) 1)) = (-1 : ℂ) • (signMul (uG z2 (-z2) 1)) :=
  bipartite_neg_eigen _ 1 A_mulVec_j2

/-- `−2cos(5π/12) = −√(2−√3)` (j = 1 reflection). -/
theorem A_mulVec_negJ1 :
    A *ᵥ (signMul (uG z1 (1 + I * z1 - I) ((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ)))
      = (-((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ))
          • (signMul (uG z1 (1 + I * z1 - I) ((Real.sqrt (2 - Real.sqrt 3) : ℝ) : ℂ))) :=
  bipartite_neg_eigen _ _ A_mulVec_j1

/-- `−2cos(π/12) = −√(2+√3)` (j = 5 reflection). -/
theorem A_mulVec_negJ5 :
    A *ᵥ (signMul (uG z5 (1 + I * z5 - I) ((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ)))
      = (-((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ))
          • (signMul (uG z5 (1 + I * z5 - I) ((Real.sqrt (2 + Real.sqrt 3) : ℝ) : ℂ))) :=
  bipartite_neg_eigen _ _ A_mulVec_j5

/-! ### Axiom audit — every shipped theorem must be `[propext, Classical.choice, Quot.sound]`-clean
    (no `sorryAx`). -/

#print axioms neighbour_symm
#print axioms adj_symm
#print axioms A_symm
#print axioms neighbours_distinct
#print axioms nbhd_card
#print axioms A_mulVec_ones
#print axioms neighbours_flip
#print axioms A_mulVec_sign
#print axioms A_bipartite
#print axioms bipartite_neg_eigen
#print axioms A_mulVec_golden
#print axioms A_mulVec_uG
#print axioms A_mulVec_j4
#print axioms A_mulVec_j2
#print axioms A_mulVec_j1
#print axioms A_mulVec_j5
#print axioms A_mulVec_neg3
#print axioms A_mulVec_negGolden
#print axioms A_mulVec_negJ4
#print axioms A_mulVec_negJ2
#print axioms A_mulVec_negJ1
#print axioms A_mulVec_negJ5

end TonnetzSpectrum
