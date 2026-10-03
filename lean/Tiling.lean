/- Tiling.lean — the DFT (Fourier) characterization of cyclic tiling over ℤ/12 (§F keystone).
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   A pair of pc-sets `A, B ⊆ ℤ/12` **tiles** the cycle when every `x ∈ ℤ/12` has a UNIQUE
   representation `x = a + b` with `a ∈ A`, `b ∈ B` (a "rhythmic canon" / perfect mosaic). The
   keystone, stated as `tiles_iff_dft`:

       A ⊕ B = ℤ/12   ⟺   |A|·|B| = 12   ∧   ∀ k ≠ 0,  Â A k = 0  ∨  Â B k = 0,

   i.e. tiling ⟺ the right cardinality product AND the zero-sets of the two DFTs cover every nonzero
   frequency, `Z(Â) ∪ Z(B̂) ⊇ {1,…,11}`.

   Proof spine (all sorry-free, axiom-clean):
   • `tileCount A B x = #{(a,b) ∈ A×B : a+b=x}` — the indicator convolution `1_A ⋆ 1_B`.
   • `dft_tileCount` — the **discrete convolution theorem**: `𝓕(tileCount A B) k = Â A k · Â B k`.
     (Mathlib's `Analysis/Fourier/Convolution.lean` is purely the CONTINUOUS Schwartz-space transform;
     there is NO `ZMod.dft`-convolution lemma, so this is proved here from the character-sum collapse,
     the same technique as `Fourier.sumcorr_eq_invDFT`.)
   • `dft_const_one` — `𝓕(fun _ => 1) k = if k = 0 then 12 else 0` (orthogonality of `stdAddChar`).
   • `Tiles A B ↔ ∀ x, tileCount A B x = 1`, then DFT-inject (`ZMod.dft` is a `LinearEquiv`):
     tiling ⟺ `Â A k · Â B k = (if k=0 then 12 else 0)` for all k, ⟺ the headline (ℂ has no zero
     divisors for the k≠0 factor, `Ahat_zero` for k=0).

   SCOPE / honesty: FIRST formalization in any proof assistant (Lean/Coq/Isabelle) of the DFT criterion
   for cyclic-group tiling. The mathematics is KNOWN — the DFT form is Amiot, *Music Through Fourier
   Space* (2016); the criterion descends from Coven–Meyerowitz (1999), lineage Hajós / de Bruijn /
   Newman. This is NOT new mathematics, and it does NOT touch Coven–Meyerowitz (T1)/(T2) or Fuglede
   (strictly harder, out of scope). The contribution is the machine-checked formalization.

   Cross-file build (Fourier.olean first, then this with LEAN_PATH), from godsil-gutman-lean env:
     MM=…/research/music-math/lean
     lake env lean --root="$MM" -o "$MM/Fourier.olean" "$MM/Fourier.lean"
     LEAN_PATH="$MM;$LEAN_PATH" lake env lean --root="$MM" "$MM/Tiling.lean" -/
import Fourier

open Finset ZMod AddChar
open scoped ZMod

namespace Tiling

open Fourier

/-- The **tiling convolution count** `(1_A ⋆ 1_B)(x) = #{(a,b) ∈ A×B : a+b = x}`: the number of ways
    to write `x` as a sum of an element of `A` and an element of `B`. -/
def tileCount (A B : Finset (ZMod 12)) (x : ZMod 12) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ B, if a + b = x then 1 else 0

/-- `A` and `B` **tile** `ℤ/12` iff every pitch class is hit exactly once by `A + B`. -/
def Tiles (A B : Finset (ZMod 12)) : Prop := ∀ x : ZMod 12, tileCount A B x = 1

/-- **The discrete convolution theorem.** The DFT of the tiling-convolution count is the pointwise
    PRODUCT of the two DFTs: `𝓕(tileCount A B) k = Â A k · Â B k`. Proved by expanding the product,
    merging the two character factors `χ(-(a k))·χ(-(b k)) = χ(-((a+b) k))`, and regrouping by the sum
    `x = a + b` (the discrete analogue of `fourier_mul_convolution_eq`, which Mathlib provides only for
    the continuous Schwartz-space transform). -/
theorem dft_tileCount (A B : Finset (ZMod 12)) (k : ZMod 12) :
    𝓕 (fun x => (tileCount A B x : ℂ)) k = Ahat A k * Ahat B k := by
  -- Both sides equal Σ_{a∈A} Σ_{b∈B} χ(-((a+b)*k)); prove each via `trans`.
  trans (∑ a ∈ A, ∑ b ∈ B, stdAddChar (-((a + b) * k)))
  · -- LHS = double sum: pull χ inside, swap sums, collapse the x-sum by the indicator.
    rw [dft_apply]
    simp only [tileCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    -- inner: Σ_x χ(-(x*k)) * (if a+b=x then 1 else 0) = χ(-((a+b)*k))
    rw [show (∑ x : ZMod 12, stdAddChar (-(x * k)) * if a + b = x then (1:ℂ) else 0)
          = ∑ x : ZMod 12, if x = a + b then stdAddChar (-((a + b) * k)) else 0 from
        Finset.sum_congr rfl fun x _ => by
          by_cases h : a + b = x
          · rw [if_pos h, if_pos h.symm, mul_one, h]
          · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]]
    rw [Finset.sum_ite_eq' Finset.univ (a + b) (fun _ => stdAddChar (-((a + b) * k)))]
    rw [if_pos (Finset.mem_univ _)]
  · -- RHS = double sum: distribute the product, merge the two characters.
    rw [Ahat_apply, Ahat_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← map_add_eq_mul]
    congr 1; ring

/-- **DFT of the constant `1`.** `𝓕(fun _ => 1) k = if k = 0 then 12 else 0` (`= 12·δ₀`), by
    orthogonality of the standard additive character: the full character sum is `12` at `k = 0` and
    vanishes for `k ≠ 0` (`Fourier.dft_one_apply_ne`). -/
theorem dft_const_one (k : ZMod 12) :
    𝓕 (fun _ : ZMod 12 => (1 : ℂ)) k = if k = 0 then (12 : ℂ) else 0 := by
  rw [dft_apply]
  simp only [smul_eq_mul, mul_one]
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    exact dft_one_apply_ne hk

/-- The constant function `1` and the convolution count have equal DFTs iff `tileCount = 1` pointwise
    (`ZMod.dft` is a `LinearEquiv`, hence injective). -/
lemma tileCount_eq_one_iff_dft_eq (A B : Finset (ZMod 12)) :
    Tiles A B ↔ (fun x => (tileCount A B x : ℂ)) = (fun _ => (1 : ℂ)) := by
  unfold Tiles
  constructor
  · intro h; funext x; rw [h x]; norm_num
  · intro h x
    have := congrFun h x
    simp only at this
    exact_mod_cast this

/-- **Tiling ⟺ DFT product is `12·δ₀`.** `A ⊕ B = ℤ/12` iff `Â A k · Â B k = if k=0 then 12 else 0`
    for every frequency `k`. (Apply the convolution theorem + DFT injectivity to `tileCount = 1`.) -/
theorem tiles_iff_dft_product (A B : Finset (ZMod 12)) :
    Tiles A B ↔ ∀ k : ZMod 12, Ahat A k * Ahat B k = if k = 0 then (12 : ℂ) else 0 := by
  rw [tileCount_eq_one_iff_dft_eq]
  constructor
  · intro h k
    rw [← dft_tileCount, h, dft_const_one]
  · intro h
    apply dft.injective
    funext k
    rw [dft_tileCount, h, dft_const_one]

/-- **§F KEYSTONE — the DFT tiling criterion over ℤ/12.**
    `A ⊕ B = ℤ/12` (every pitch class uniquely a sum `a+b`, `a∈A`, `b∈B`)  ⟺
        `|A|·|B| = 12`   ∧   `∀ k ≠ 0,  Â A k = 0 ∨ Â B k = 0`.
    The cardinality condition is the `k = 0` Fourier coefficient (`Ahat_zero`: `Â·0 = card`); the
    zero-set condition is the `k ≠ 0` coefficients, where `ℂ` has no zero divisors so the product
    vanishes iff a factor does. First formalization in any proof assistant; KNOWN math (Amiot 2016 /
    Coven–Meyerowitz 1999), NOT new. -/
theorem tiles_iff_dft (A B : Finset (ZMod 12)) :
    Tiles A B ↔ (A.card * B.card = 12 ∧ ∀ k ≠ 0, Ahat A k = 0 ∨ Ahat B k = 0) := by
  rw [tiles_iff_dft_product]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- k = 0: Â A 0 · Â B 0 = |A|·|B| = 12, in ℂ; cast back to ℕ
      have h0 := h 0
      rw [if_pos rfl, Ahat_zero, Ahat_zero] at h0
      have : ((A.card * B.card : ℕ) : ℂ) = ((12 : ℕ) : ℂ) := by push_cast; rw [h0]
      exact_mod_cast this
    · intro k hk
      have hk0 := h k
      rw [if_neg hk] at hk0
      exact mul_eq_zero.mp hk0
  · rintro ⟨hcard, hzero⟩ k
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, Ahat_zero, Ahat_zero]
      have : ((A.card * B.card : ℕ) : ℂ) = ((12 : ℕ) : ℂ) := by exact_mod_cast hcard
      push_cast at this ⊢
      rw [this]
    · rw [if_neg hk]
      rcases hzero k hk with h | h <;> rw [h] <;> ring

/-! ### Witnesses — a positive tiling and a same-cardinality NON-tiling, both via the criterion. -/

/-- **Positive witness.** `A = {0,1,2,3}` (a chromatic tetrachord) and `B = {0,4,8}` (the augmented
    triad) **tile** ℤ/12: `4·3 = 12` and every pc is uniquely `a+b`. The classic "block canon". -/
theorem chromatic_aug_tiles : Tiles {0, 1, 2, 3} {0, 4, 8} := by
  intro x; revert x; decide

/-- The positive witness also passes the **Fourier criterion** directly: `4·3 = 12` and at every
    nonzero frequency one of the two DFTs vanishes (`B̂` kills `k ∈ {1,2,4,5,7,8,10,11}` by the
    augmented-triad symmetry, `Â` kills `k ∈ {3,6,9}`). -/
theorem chromatic_aug_tiles' :
    ({0, 1, 2, 3} : Finset (ZMod 12)).card * ({0, 4, 8} : Finset (ZMod 12)).card = 12 ∧
      ∀ k ≠ 0, Ahat ({0,1,2,3}) k = 0 ∨ Ahat ({0,4,8}) k = 0 :=
  (tiles_iff_dft _ _).mp chromatic_aug_tiles

/-- **Negative witness.** `A = {0,1,2,3}` and `B = {0,1,8}` do NOT tile, even though `4·3 = 12`:
    the sum `A + B` covers `0` twice and misses `6`. So the right cardinality product is NOT
    sufficient — the zero-set condition is the real content. -/
theorem chromatic_badtriad_not_tiles : ¬ Tiles {0, 1, 2, 3} {0, 1, 8} := by
  unfold Tiles
  intro h
  have := h 6
  revert this
  decide

/-- The negative witness fails the **Fourier criterion** at the cardinality-correct level precisely
    in the zero-set clause: there is a nonzero `k` with both `Â A k ≠ 0` and `Â B k ≠ 0`. -/
theorem chromatic_badtriad_fails_zeroset :
    ¬ (∀ k ≠ 0, Ahat ({0,1,2,3} : Finset (ZMod 12)) k = 0 ∨ Ahat ({0,1,8}) k = 0) := by
  intro h
  exact chromatic_badtriad_not_tiles
    ((tiles_iff_dft _ _).mpr ⟨by decide, h⟩)

end Tiling

-- Axiom audit (expect: [propext, Classical.choice, Quot.sound], no sorryAx).
#print axioms Tiling.dft_tileCount
#print axioms Tiling.dft_const_one
#print axioms Tiling.tiles_iff_dft_product
#print axioms Tiling.tiles_iff_dft
#print axioms Tiling.chromatic_aug_tiles
#print axioms Tiling.chromatic_aug_tiles'
#print axioms Tiling.chromatic_badtriad_not_tiles
#print axioms Tiling.chromatic_badtriad_fails_zeroset
