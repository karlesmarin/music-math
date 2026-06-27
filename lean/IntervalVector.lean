/- IntervalVector.lean — the interval vector of a pitch-class set and its T/I-invariance.
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   Formalizes §B.1 of FORMULAS.md: for a pitch-class set A ⊆ ℤ/12, the interval vector counts how
   many times each interval class k ∈ {1,…,6} occurs as a difference of two notes of A, and this
   count is invariant under transposition Tₙ and inversion I. We prove the invariance for the
   "raw" (ordered-pair) count `IVraw`; the textbook vector is `IVraw A k / 2`.

   The interval class is written `ivc d = min d.val (-d).val`, which makes neg-invariance literally
   `min_comm`. Invariance is then proved once for any difference-class-preserving embedding of ℤ/12,
   and Tₙ / I follow as one-liners.

   Fast-loop build (specific imports): lake env lean IntervalVector.lean (from godsil-gutman env). -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.Ring

open Finset

namespace IntervalVector

/-- Interval class of a pitch-class difference: `min(d, 12−d)`, value in `0..6`.
    Written as `min d.val (-d).val` so that neg-invariance is just `min_comm`. -/
def ivc (d : ZMod 12) : ℕ := min d.val (-d).val

@[simp] lemma ivc_neg (d : ZMod 12) : ivc (-d) = ivc d := by
  unfold ivc; rw [neg_neg, min_comm]

/-- Raw interval vector: number of ORDERED pairs `(a,b) ∈ A×A` with interval class `k`.
    The textbook interval vector is `IVraw A k / 2` for `k = 1..6` (each unordered pair twice). -/
def IVraw (A : Finset (ZMod 12)) (k : ℕ) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if ivc (a - b) = k then 1 else 0

/-- C major triad `{0,4,7}`: ordered counts are 2 at k=3,4,5 and 0 elsewhere, i.e. the textbook
    interval vector ⟨0 0 1 1 1 0⟩. -/
example : IVraw {0, 4, 7} 4 = 2 := by decide
example : IVraw {0, 4, 7} 5 = 2 := by decide
example : IVraw {0, 4, 7} 1 = 0 := by decide

/-- Invariance under any embedding of ℤ/12 that preserves the interval class of differences. -/
lemma IVraw_map (e : ZMod 12 ↪ ZMod 12)
    (he : ∀ a b : ZMod 12, ivc (e a - e b) = ivc (a - b)) (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw (A.map e) k = IVraw A k := by
  simp only [IVraw, Finset.sum_map]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [he a b]

/-- Transposition `Tₙ : a ↦ a + n`. -/
def tpose (n : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(· + n), add_left_injective n⟩
/-- Inversion `I : a ↦ −a`. -/
def invert (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(-·), neg_injective⟩

/-- **The interval vector is invariant under transposition.** -/
theorem IVraw_tpose (n : ZMod 12) (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw (tpose n A) k = IVraw A k :=
  IVraw_map _ (fun a b => by
    simp only [Function.Embedding.coeFn_mk]
    rw [show a + n - (b + n) = a - b from by ring]) A k

/-- **The interval vector is invariant under inversion.** -/
theorem IVraw_invert (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw (invert A) k = IVraw A k :=
  IVraw_map _ (fun a b => by
    simp only [Function.Embedding.coeFn_mk]
    rw [show -a - -b = -(a - b) from by ring, ivc_neg]) A k

end IntervalVector
