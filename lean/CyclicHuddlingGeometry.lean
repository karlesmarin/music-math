import CyclicHuddling
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!+# Projection geometry for cyclic Huddling

The circle is cut at the boundary of a selected arc. Cosine monotonicity
separates the arc from its complement, including boundary ties.
-/

open Finset ZMod Complex

namespace CyclicHuddling

lemma cos_ge_of_between {x t : ℝ} (ht : t ≤ Real.pi)
    (hx₁ : -t ≤ x) (hx₂ : x ≤ t) :
    Real.cos t ≤ Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) ht
    (abs_le.mpr ⟨hx₁, hx₂⟩)

lemma cos_le_of_between {x t : ℝ} (ht₀ : 0 ≤ t)
    (hx₁ : t ≤ x) (hx₂ : x ≤ 2 * Real.pi - t) :
    Real.cos x ≤ Real.cos t := by
  by_cases hx : x ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ht₀ hx hx₁
  · rw [← Real.cos_two_pi_sub x]
    apply Real.cos_le_cos_of_nonneg_of_le_pi ht₀
    · linarith
    · linarith

/-- A rotated grid always has a cut with residual angle in a prescribed cell. -/
lemma exists_grid_cut (θ t h : ℝ) (hh : 0 < h) :
    ∃ s : ℤ, t - h ≤ θ - h * s ∧ θ - h * s ≤ t := by
  refine ⟨⌈(θ - t) / h⌉, ?_, ?_⟩
  · have hs := Int.ceil_lt_add_one ((θ - t) / h)
    have hp := mul_lt_mul_of_pos_left hs hh
    have he : h * ((θ - t) / h) = θ - t := by field_simp
    rw [mul_add, he, mul_one] at hp
    linarith
  · have hs := Int.le_ceil ((θ - t) / h)
    have hp := mul_le_mul_of_nonneg_left hs hh.le
    have he : h * ((θ - t) / h) = θ - t := by field_simp
    rw [he] at hp
    linarith

#print axioms cos_ge_of_between
#print axioms cos_le_of_between
#print axioms exists_grid_cut

end CyclicHuddling
