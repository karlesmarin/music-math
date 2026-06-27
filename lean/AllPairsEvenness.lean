/- AllPairsEvenness.lean — the all-pairs convex-energy uniqueness of maximal evenness in ℤ/12,
   across cardinalities k ∈ {5,6,7,8}, in its V-INDEPENDENT form.
   Author: Carles Marín  <karlesmarin@gmail.com>   (Claude, Anthropic, as AI assistant)

   First ITP formalization of the all-pairs convex-energy uniqueness of maximal evenness in ℤ/12;
   V-INDEPENDENT; classical math (Douthett–Krantz, JMP 1996/1998; JCO 2007), NOT new — and
   STRICTLY STRONGER than the step-gap `MaximalEvenness.lean` (which is degenerate: its
   nearest-neighbour energy is constant across all balanced sets, so it does NOT single out the
   maximally-even set; here the ALL-PAIRS energy `Σ_{pairs} V(circ-dist)` does, for EVERY admissible
   potential simultaneously).

   COVERAGE — all four chromatic-scale cardinalities share the SAME Abel engine; only the
   per-cardinality maximally-even set + its finite census change:
   • k=5  pentatonic  P = {0,2,4,7,9}        iv ⟨0,3,2,1,4,0⟩  orbit 12  single-V min E₀=132
   • k=6  whole-tone  W = {0,2,4,6,8,10}      iv ⟨0,6,0,6,0,3⟩  orbit  2  single-V min E₀=207
   • k=7  diatonic    D = {0,2,4,5,7,9,11}    iv ⟨2,5,4,3,6,1⟩  orbit 12  single-V min E₀=313
   • k=8  octatonic   O = {0,1,3,4,6,7,9,10}  iv ⟨4,4,8,4,4,4⟩  orbit  3  single-V min E₀=428

   The engine is a double Abel summation (summation-by-parts, `abel_bridge`): for any two 7-subsets
   `A`, `D` the interval-vector difference `d = iv A − iv D` has `∑ d = 0` (both have C(7,2)=21
   pairs), so `E(V,A) − E(V,D) = ∑ j, d_j·V(j+1)` collapses to a sum of DOUBLE-cumulative sums
   `DD_j` against the second differences (convexity) of `V`, plus one decreasing boundary term.
   A finite census (`native_decide`) shows `DD_j ≥ 0` for every 7-subset and `DD_j > 0` off the
   T/I-orbit of the diatonic. Hence the diatonic is the unique all-pairs ground state for ALL
   admissible `V` at once.

   Delivered, sorry-free:
   • `abel_bridge`              : double summation-by-parts identity (∑d=0)        — AXIOM-CLEAN
   • `abel_nonneg` / `abel_pos` : ≥0 / >0 from DD≥0 + convex/decreasing            — AXIOM-CLEAN
   • `dg`/`E_sub_g`/`E_eq_g`    : generic reference-set engine (k-independent)     — AXIOM-CLEAN
   • `groundStateG` / `uniqueG` : generic V-independent ≤ / uniqueness from census — AXIOM-CLEAN
   • `item1_min` / `item1_unique` : single-V census — `E₀ A ≥ 313`, `=313 ⟺ orbit` — native_decide
   • `{pentatonic,wholetone,diatonic,octatonic}_ground_state` : ∀ admissible V, ME minimizes E V
   • `{pentatonic,wholetone,diatonic,octatonic}_unique`       : ∀ strict V, `E V ME = E V A ⟺ orbit`
   (the four ground_state/unique pairs are the V-INDEPENDENT capstones for k=5,6,7,8 — native_decide)

   AXIOM REPORT (see `#print axioms` at end): the Abel + generic engine layer (`abel_bridge`,
   `abel_nonneg`, `abel_pos`, `E_sub_g`, `E_eq_g`, `groundStateG`, `uniqueG`) is axiom-clean
   `[propext, Classical.choice, Quot.sound]`. The census/capstones carry the extra native
   `native_decide` axiom (≡ `Lean.ofReduceBool`) over the k-subsets of ℤ/12 — acceptable for a
   finite computation, flagged explicitly.

   Fast-loop build (godsil-gutman-lean env):
     lake env lean "E:/proyectos/Curiosity/research/music-math/lean/AllPairsEvenness.lean" -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

open Finset

namespace AllPairsEvenness

/-! ### Definitions -/

/-- Circular distance in `ℤ/12`: `min(|a−b|, 12−|a−b|)`, a value in `0..6`. -/
def cdist (a b : ZMod 12) : ℕ := min (a - b).val (b - a).val

/-- Interval vector entry at distance `k` (textbook convention): the number of UNORDERED pairs
    `{a,b} ⊆ A` with circular distance `k`. Each unordered pair is counted twice in `A ×ˢ A`
    (as `(a,b)` and `(b,a)`, since `cdist` is symmetric), so we divide by 2. -/
def iv (A : Finset (ZMod 12)) (k : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => cdist p.1 p.2 = k)).card / 2

/-- The diatonic collection `{0,2,4,5,7,9,11} ⊂ ℤ/12`. Its interval vector is the classic
    `⟨2,5,4,3,6,1⟩` (verified by `decide`, see `iv_D`). -/
def D : Finset (ZMod 12) := {0, 2, 4, 5, 7, 9, 11}

/-- Transposition `Tₙ : a ↦ a + n`. -/
def tpose (n : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(· + n), add_left_injective n⟩

/-- Inversion `I_j : a ↦ j − a` (axis `j/2`). -/
def inv (j : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(j - ·), fun a b h => by have h' : j - a = j - b := h; linear_combination -h'⟩

/-- The T/I-orbit of the diatonic: all 12 transposes ∪ all inversions (= 12 distinct sets,
    the diatonic being inversionally symmetric). -/
def orbitTI : Finset (Finset (ZMod 12)) :=
  ((univ : Finset (ZMod 12)).image (fun k => tpose k D))
    ∪ ((univ : Finset (ZMod 12)).image (fun j => inv j D))

/-- The T/I-orbit of an arbitrary reference set `R`: all 12 transposes ∪ all 12 inversions. -/
def orbitOf (R : Finset (ZMod 12)) : Finset (Finset (ZMod 12)) :=
  ((univ : Finset (ZMod 12)).image (fun k => tpose k R))
    ∪ ((univ : Finset (ZMod 12)).image (fun j => inv j R))

/-- The pentatonic collection `{0,2,4,7,9} ⊂ ℤ/12` (`iv = ⟨0,3,2,1,4,0⟩`, T/I-orbit size 12). -/
def P : Finset (ZMod 12) := {0, 2, 4, 7, 9}

/-- The whole-tone collection `{0,2,4,6,8,10} ⊂ ℤ/12` (`iv = ⟨0,6,0,6,0,3⟩`, T/I-orbit size 2). -/
def W : Finset (ZMod 12) := {0, 2, 4, 6, 8, 10}

/-- The octatonic collection `{0,1,3,4,6,7,9,10} ⊂ ℤ/12` (`iv = ⟨4,4,8,4,4,4⟩`, orbit size 3). -/
def O : Finset (ZMod 12) := {0, 1, 3, 4, 6, 7, 9, 10}

/-- Integer interval-vector difference from the diatonic: `d_j = iv A (j+1) − iv D (j+1)`. -/
def dvec (A : Finset (ZMod 12)) : ℕ → ℤ := fun j => (iv A (j + 1) : ℤ) - (iv D (j + 1) : ℤ)

/-- Double-cumulative sum `DD_j = Σ_{l≤j} (j+1−l)·d_l = Σ_{l≤j} Σ_{i≤l} d_i` (single-sum closed
    form of the double Abel cumulative). -/
def DD (d : ℕ → ℤ) (j : ℕ) : ℤ := ∑ l ∈ Finset.range (j + 1), ((j + 1 : ℤ) - l) * d l

/-- All-pairs energy of `A` for a real potential `V : ℕ → ℝ` (distance → energy):
    `E V A = Σ_{k=1..6} iv A k · V k`. -/
noncomputable def E (V : ℕ → ℝ) (A : Finset (ZMod 12)) : ℝ :=
  ∑ j ∈ Finset.range 6, (iv A (j + 1) : ℝ) * V (j + 1)

/-! ### Item 2 — the Abel bridge (general, V-independent, axiom-clean) -/

/-- **Double summation-by-parts (the engine).** For any `d : ℕ → ℤ` with `d₀+⋯+d₅ = 0` and any
    `V : ℕ → ℝ`,
    `Σ_{j<6} d_j·V(j+1) = Σ_{j<4} DD_j·(V(j+1) − 2V(j+2) + V(j+3)) + DD₄·(V 5 − V 6)`.
    Both boundary terms of the first Abel pass vanish because `∑ d = 0`; the residual `DD₄·(V5−V6)`
    is the surviving (decreasing) boundary of the second pass. Pure algebra — AXIOM-CLEAN. -/
theorem abel_bridge (d : ℕ → ℤ) (V : ℕ → ℝ)
    (hsum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 = 0) :
    ∑ j ∈ Finset.range 6, (d j : ℝ) * V (j + 1)
      = (∑ j ∈ Finset.range 4, (DD d j : ℝ) * (V (j + 1) - 2 * V (j + 2) + V (j + 3)))
        + (DD d 4 : ℝ) * (V 5 - V 6) := by
  have hsumR : (d 0 : ℝ) + d 1 + d 2 + d 3 + d 4 + d 5 = 0 := by exact_mod_cast hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, DD]
  push_cast
  linear_combination (V 6) * hsumR

/-- The four convexity windows expanded out of the range-4 sum (helper for the bounds). -/
private lemma bridge_sum_expand (d : ℕ → ℤ) (V : ℕ → ℝ) :
    (∑ j ∈ Finset.range 4, (DD d j : ℝ) * (V (j + 1) - 2 * V (j + 2) + V (j + 3)))
      = (DD d 0 : ℝ) * (V 1 - 2 * V 2 + V 3) + (DD d 1 : ℝ) * (V 2 - 2 * V 3 + V 4)
        + (DD d 2 : ℝ) * (V 3 - 2 * V 4 + V 5) + (DD d 3 : ℝ) * (V 4 - 2 * V 5 + V 6) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- **Nonnegativity (V-independent ≥).** With `DD_j ≥ 0` (j=0..4), the four second differences
    `≥ 0` (convexity) and `V 6 ≤ V 5` (decreasing top), the energy gap is `≥ 0`. AXIOM-CLEAN. -/
theorem abel_nonneg (d : ℕ → ℤ) (V : ℕ → ℝ)
    (hsum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 = 0)
    (h0 : 0 ≤ DD d 0) (h1 : 0 ≤ DD d 1) (h2 : 0 ≤ DD d 2) (h3 : 0 ≤ DD d 3) (h4 : 0 ≤ DD d 4)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5) :
    0 ≤ ∑ j ∈ Finset.range 6, (d j : ℝ) * V (j + 1) := by
  rw [abel_bridge d V hsum, bridge_sum_expand d V]
  have t0 := mul_nonneg (show (0 : ℝ) ≤ (DD d 0 : ℝ) by exact_mod_cast h0) hc0
  have t1 := mul_nonneg (show (0 : ℝ) ≤ (DD d 1 : ℝ) by exact_mod_cast h1) hc1
  have t2 := mul_nonneg (show (0 : ℝ) ≤ (DD d 2 : ℝ) by exact_mod_cast h2) hc2
  have t3 := mul_nonneg (show (0 : ℝ) ≤ (DD d 3 : ℝ) by exact_mod_cast h3) hc3
  have t4 := mul_nonneg (show (0 : ℝ) ≤ (DD d 4 : ℝ) by exact_mod_cast h4)
    (show (0 : ℝ) ≤ V 5 - V 6 by linarith)
  linarith [t0, t1, t2, t3, t4]

/-- **Strict positivity (V-independent >).** Strictly convex (`> 0` second differences), strictly
    decreasing top (`V 6 < V 5`), `DD_j ≥ 0`, and SOME `DD_j > 0` ⟹ strictly positive gap.
    AXIOM-CLEAN. -/
theorem abel_pos (d : ℕ → ℤ) (V : ℕ → ℝ)
    (hsum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 = 0)
    (h0 : 0 ≤ DD d 0) (h1 : 0 ≤ DD d 1) (h2 : 0 ≤ DD d 2) (h3 : 0 ≤ DD d 3) (h4 : 0 ≤ DD d 4)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (hex : 0 < DD d 0 ∨ 0 < DD d 1 ∨ 0 < DD d 2 ∨ 0 < DD d 3 ∨ 0 < DD d 4) :
    0 < ∑ j ∈ Finset.range 6, (d j : ℝ) * V (j + 1) := by
  rw [abel_bridge d V hsum, bridge_sum_expand d V]
  -- all five products are ≥ 0
  have t0 := mul_nonneg (show (0 : ℝ) ≤ (DD d 0 : ℝ) by exact_mod_cast h0) hc0.le
  have t1 := mul_nonneg (show (0 : ℝ) ≤ (DD d 1 : ℝ) by exact_mod_cast h1) hc1.le
  have t2 := mul_nonneg (show (0 : ℝ) ≤ (DD d 2 : ℝ) by exact_mod_cast h2) hc2.le
  have t3 := mul_nonneg (show (0 : ℝ) ≤ (DD d 3 : ℝ) by exact_mod_cast h3) hc3.le
  have t4 := mul_nonneg (show (0 : ℝ) ≤ (DD d 4 : ℝ) by exact_mod_cast h4)
    (show (0 : ℝ) ≤ V 5 - V 6 by linarith)
  -- one of them is > 0
  rcases hex with h | h | h | h | h
  · have := mul_pos (show (0 : ℝ) < (DD d 0 : ℝ) by exact_mod_cast h) hc0; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 1 : ℝ) by exact_mod_cast h) hc1; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 2 : ℝ) by exact_mod_cast h) hc2; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 3 : ℝ) by exact_mod_cast h) hc3; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 4 : ℝ) by exact_mod_cast h)
      (show (0 : ℝ) < V 5 - V 6 by linarith); linarith

/-! ### The finite censuses (native_decide over the 792 seven-subsets) -/

/-- `iv D = ⟨2,5,4,3,6,1⟩` — the classic diatonic interval vector. -/
theorem iv_D : iv D 1 = 2 ∧ iv D 2 = 5 ∧ iv D 3 = 4 ∧ iv D 4 = 3 ∧ iv D 5 = 6 ∧ iv D 6 = 1 := by
  decide

/-- Every 7-subset has `C(7,2)=21` unordered pairs, so `∑ d = 0`. (Census.) -/
theorem census_hsum (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    dvec A 0 + dvec A 1 + dvec A 2 + dvec A 3 + dvec A 4 + dvec A 5 = 0 := by
  revert A hA
  native_decide

/-- The double-cumulative sums are nonnegative for EVERY 7-subset. (Census — the Abel engine.) -/
theorem census_DD (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    0 ≤ DD (dvec A) 0 ∧ 0 ≤ DD (dvec A) 1 ∧ 0 ≤ DD (dvec A) 2 ∧ 0 ≤ DD (dvec A) 3
      ∧ 0 ≤ DD (dvec A) 4 := by
  revert A hA
  native_decide

/-- OFF the T/I-orbit of the diatonic, some double-cumulative sum is strictly positive. (Census —
    this is what makes the diatonic the UNIQUE minimizer.) -/
theorem census_offorbit (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7)
    (hoff : A ∉ orbitTI) :
    0 < DD (dvec A) 0 ∨ 0 < DD (dvec A) 1 ∨ 0 < DD (dvec A) 2 ∨ 0 < DD (dvec A) 3
      ∨ 0 < DD (dvec A) 4 := by
  revert A hA hoff
  native_decide

/-- ON the orbit, the interval vector equals the diatonic's, so `dvec = 0`. (Census.) -/
theorem census_onorbit (A : Finset (ZMod 12)) (hA : A ∈ orbitTI) :
    iv A 1 = iv D 1 ∧ iv A 2 = iv D 2 ∧ iv A 3 = iv D 3 ∧ iv A 4 = iv D 4 ∧ iv A 5 = iv D 5
      ∧ iv A 6 = iv D 6 := by
  revert A hA
  native_decide

/-! ### Item 1 — single-V uniqueness via finite census (anchor) -/

/-- The integer admissible potential `V₀(k) = (7−k)²` (strictly convex, decreasing: 36,25,16,9,4,1)
    and its all-pairs energy over ℕ: `E₀ A = Σ_{k=1..6} iv A k · (7−k)²`. -/
def E0 (A : Finset (ZMod 12)) : ℕ := ∑ j ∈ Finset.range 6, iv A (j + 1) * (7 - (j + 1)) ^ 2

/-- `E₀ D = 313` (= 2·36+5·25+4·16+3·9+6·4+1·1). -/
theorem E0_D : E0 D = 313 := by decide

/-- **Item 1a (anchor).** Among all 7-subsets of `ℤ/12`, the all-pairs energy `E₀` is `≥ 313`.
    (Census; `native_decide`.) -/
theorem item1_min (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    313 ≤ E0 A := by
  revert A hA
  native_decide

/-- **Item 1b (anchor).** The minimum `313` is attained EXACTLY on the 12 T/I-transposes of the
    diatonic: `E₀ A = 313 ⟺ A ∈ orbitTI`. (Census; `native_decide`.) -/
theorem item1_unique (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    E0 A = 313 ↔ A ∈ orbitTI := by
  revert A hA
  native_decide

/-! ### Item 3 — V-independent uniqueness at (7,12) (capstone) -/

/-- Energy gap as an interval-vector sum: `E V A − E V D = Σ_{j<6} dvec_j · V(j+1)`. -/
lemma E_sub (V : ℕ → ℝ) (A : Finset (ZMod 12)) :
    E V A - E V D = ∑ j ∈ Finset.range 6, (dvec A j : ℝ) * V (j + 1) := by
  unfold E
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold dvec
  push_cast
  ring

/-- On the orbit, the energy gap vanishes for any `V` (the interval vector is T/I-invariant). -/
lemma E_eq_of_mem_orbit (V : ℕ → ℝ) (A : Finset (ZMod 12)) (hA : A ∈ orbitTI) : E V A = E V D := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := census_onorbit A hA
  unfold E
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e1, e2, e3, e4, e5, e6]

/-- **Item 3, the ≥ half (V-INDEPENDENT ground state).** For EVERY decreasing-convex potential `V`,
    the diatonic minimizes the all-pairs energy: `E V D ≤ E V A` for every 7-subset `A`. The single
    inequality holds simultaneously for all admissible `V` — this is the V-independence. -/
theorem diatonic_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    E V D ≤ E V A := by
  have hsum := census_hsum A hA
  obtain ⟨h0, h1, h2, h3, h4⟩ := census_DD A hA
  have key : 0 ≤ ∑ j ∈ Finset.range 6, (dvec A j : ℝ) * V (j + 1) :=
    abel_nonneg (dvec A) V hsum h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec
  have := E_sub V A
  linarith

/-- **Item 3, the capstone (V-INDEPENDENT UNIQUENESS).** For EVERY STRICTLY convex, strictly
    decreasing potential `V`, the diatonic is the UNIQUE all-pairs ground state: `E V D = E V A`
    holds iff `A` is a transposition or inversion of the diatonic. One statement, all admissible
    `V` at once — the headline of Douthett–Krantz maximal evenness. -/
theorem diatonic_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    E V D = E V A ↔ A ∈ orbitTI := by
  constructor
  · -- equality ⟹ in orbit (else strict, contradiction)
    intro heq
    by_contra hoff
    have hsum := census_hsum A hA
    obtain ⟨h0, h1, h2, h3, h4⟩ := census_DD A hA
    have hex := census_offorbit A hA hoff
    have key : 0 < ∑ j ∈ Finset.range 6, (dvec A j : ℝ) * V (j + 1) :=
      abel_pos (dvec A) V hsum h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec hex
    have := E_sub V A
    linarith
  · -- in orbit ⟹ equality
    intro hmem
    exact (E_eq_of_mem_orbit V A hmem).symm

/-! ### Generic reference-set engine (k-independent) -/

/-- Integer interval-vector difference from an arbitrary reference set `R`:
    `dg R A j = iv A (j+1) − iv R (j+1)`. (The diatonic-specific `dvec` is `dg D`.) -/
def dg (R A : Finset (ZMod 12)) : ℕ → ℤ :=
  fun j => (iv A (j + 1) : ℤ) - (iv R (j + 1) : ℤ)

/-- Energy gap against an arbitrary reference: `E V A − E V R = Σ_{j<6} dg R A j · V(j+1)`. -/
lemma E_sub_g (V : ℕ → ℝ) (R A : Finset (ZMod 12)) :
    E V A - E V R = ∑ j ∈ Finset.range 6, (dg R A j : ℝ) * V (j + 1) := by
  unfold E
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold dg
  push_cast
  ring

/-- When `iv A` agrees with `iv R` on all six classes, the energy is equal for any `V`. -/
lemma E_eq_g (V : ℕ → ℝ) (R A : Finset (ZMod 12))
    (e1 : iv A 1 = iv R 1) (e2 : iv A 2 = iv R 2) (e3 : iv A 3 = iv R 3)
    (e4 : iv A 4 = iv R 4) (e5 : iv A 5 = iv R 5) (e6 : iv A 6 = iv R 6) :
    E V A = E V R := by
  unfold E
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e1, e2, e3, e4, e5, e6]

/-- **Generic V-independent ground state.** Given the `∑dg=0` and `DD ≥ 0` censuses over a family
    `S`, the reference `R` minimizes the all-pairs energy over `S` for every decreasing-convex `V`. -/
theorem groundStateG (R : Finset (ZMod 12)) (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (S : Finset (Finset (ZMod 12)))
    (hsum : ∀ A ∈ S, dg R A 0 + dg R A 1 + dg R A 2 + dg R A 3 + dg R A 4 + dg R A 5 = 0)
    (hDD : ∀ A ∈ S, 0 ≤ DD (dg R A) 0 ∧ 0 ≤ DD (dg R A) 1 ∧ 0 ≤ DD (dg R A) 2
      ∧ 0 ≤ DD (dg R A) 3 ∧ 0 ≤ DD (dg R A) 4)
    (A : Finset (ZMod 12)) (hA : A ∈ S) :
    E V R ≤ E V A := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hDD A hA
  have key := abel_nonneg (dg R A) V (hsum A hA) h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec
  have := E_sub_g V R A
  linarith

/-- **Generic V-independent uniqueness.** Given the `∑dg=0`, `DD ≥ 0`, off-orbit `DD>0` and
    on-orbit `iv`-agreement censuses, `R` is the unique all-pairs ground state over `S` for every
    strictly convex, strictly decreasing `V`. -/
theorem uniqueG (R : Finset (ZMod 12)) (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (S orb : Finset (Finset (ZMod 12)))
    (hsum : ∀ A ∈ S, dg R A 0 + dg R A 1 + dg R A 2 + dg R A 3 + dg R A 4 + dg R A 5 = 0)
    (hDD : ∀ A ∈ S, 0 ≤ DD (dg R A) 0 ∧ 0 ≤ DD (dg R A) 1 ∧ 0 ≤ DD (dg R A) 2
      ∧ 0 ≤ DD (dg R A) 3 ∧ 0 ≤ DD (dg R A) 4)
    (hoff : ∀ A ∈ S, A ∉ orb → 0 < DD (dg R A) 0 ∨ 0 < DD (dg R A) 1 ∨ 0 < DD (dg R A) 2
      ∨ 0 < DD (dg R A) 3 ∨ 0 < DD (dg R A) 4)
    (hon : ∀ A ∈ orb, iv A 1 = iv R 1 ∧ iv A 2 = iv R 2 ∧ iv A 3 = iv R 3
      ∧ iv A 4 = iv R 4 ∧ iv A 5 = iv R 5 ∧ iv A 6 = iv R 6)
    (A : Finset (ZMod 12)) (hA : A ∈ S) :
    E V R = E V A ↔ A ∈ orb := by
  constructor
  · intro heq
    by_contra hoffA
    obtain ⟨h0, h1, h2, h3, h4⟩ := hDD A hA
    have hex := hoff A hA hoffA
    have key := abel_pos (dg R A) V (hsum A hA) h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec hex
    have := E_sub_g V R A
    linarith
  · intro hmem
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hon A hmem
    exact (E_eq_g V R A e1 e2 e3 e4 e5 e6).symm

/-! ### k = 5 — pentatonic `{0,2,4,7,9}` (orbit size 12) -/

/-- `iv P = ⟨0,3,2,1,4,0⟩`. -/
theorem iv_P : iv P 1 = 0 ∧ iv P 2 = 3 ∧ iv P 3 = 2 ∧ iv P 4 = 1 ∧ iv P 5 = 4 ∧ iv P 6 = 0 := by
  decide

theorem census_hsum_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5,
    dg P A 0 + dg P A 1 + dg P A 2 + dg P A 3 + dg P A 4 + dg P A 5 = 0 := by
  native_decide

theorem census_DD_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5,
    0 ≤ DD (dg P A) 0 ∧ 0 ≤ DD (dg P A) 1 ∧ 0 ≤ DD (dg P A) 2 ∧ 0 ≤ DD (dg P A) 3
      ∧ 0 ≤ DD (dg P A) 4 := by
  native_decide

theorem census_offorbit_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5, A ∉ orbitOf P →
    0 < DD (dg P A) 0 ∨ 0 < DD (dg P A) 1 ∨ 0 < DD (dg P A) 2 ∨ 0 < DD (dg P A) 3
      ∨ 0 < DD (dg P A) 4 := by
  native_decide

theorem census_onorbit_P : ∀ A ∈ orbitOf P,
    iv A 1 = iv P 1 ∧ iv A 2 = iv P 2 ∧ iv A 3 = iv P 3 ∧ iv A 4 = iv P 4 ∧ iv A 5 = iv P 5
      ∧ iv A 6 = iv P 6 := by
  native_decide

/-- Single-V anchor: `E₀ P = 132` and `E₀ A = 132 ⟺ A ∈ orbit` over all 5-subsets. -/
theorem item1_min_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5, 132 ≤ E0 A := by
  native_decide

theorem item1_unique_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5,
    E0 A = 132 ↔ A ∈ orbitOf P := by
  native_decide

/-- **Pentatonic ground state (V-INDEPENDENT).** For every decreasing-convex `V`, the pentatonic
    minimizes the all-pairs energy over all 5-subsets of `ℤ/12`. -/
theorem pentatonic_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 5) :
    E V P ≤ E V A :=
  groundStateG P V hc0 hc1 hc2 hc3 hdec _ census_hsum_P census_DD_P A hA

/-- **Pentatonic uniqueness (V-INDEPENDENT).** For every strictly convex, strictly decreasing `V`,
    the pentatonic is the unique all-pairs ground state up to T/I. -/
theorem pentatonic_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 5) :
    E V P = E V A ↔ A ∈ orbitOf P :=
  uniqueG P V hc0 hc1 hc2 hc3 hdec _ _ census_hsum_P census_DD_P census_offorbit_P
    census_onorbit_P A hA

/-! ### k = 8 — octatonic `{0,1,3,4,6,7,9,10}` (orbit size 3) -/

/-- `iv O = ⟨4,4,8,4,4,4⟩`. -/
theorem iv_O : iv O 1 = 4 ∧ iv O 2 = 4 ∧ iv O 3 = 8 ∧ iv O 4 = 4 ∧ iv O 5 = 4 ∧ iv O 6 = 4 := by
  decide

theorem census_hsum_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8,
    dg O A 0 + dg O A 1 + dg O A 2 + dg O A 3 + dg O A 4 + dg O A 5 = 0 := by
  native_decide

theorem census_DD_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8,
    0 ≤ DD (dg O A) 0 ∧ 0 ≤ DD (dg O A) 1 ∧ 0 ≤ DD (dg O A) 2 ∧ 0 ≤ DD (dg O A) 3
      ∧ 0 ≤ DD (dg O A) 4 := by
  native_decide

theorem census_offorbit_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8, A ∉ orbitOf O →
    0 < DD (dg O A) 0 ∨ 0 < DD (dg O A) 1 ∨ 0 < DD (dg O A) 2 ∨ 0 < DD (dg O A) 3
      ∨ 0 < DD (dg O A) 4 := by
  native_decide

theorem census_onorbit_O : ∀ A ∈ orbitOf O,
    iv A 1 = iv O 1 ∧ iv A 2 = iv O 2 ∧ iv A 3 = iv O 3 ∧ iv A 4 = iv O 4 ∧ iv A 5 = iv O 5
      ∧ iv A 6 = iv O 6 := by
  native_decide

/-- Single-V anchor: `E₀ O = 428` and `E₀ A = 428 ⟺ A ∈ orbit` over all 8-subsets. -/
theorem item1_min_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8, 428 ≤ E0 A := by
  native_decide

theorem item1_unique_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8,
    E0 A = 428 ↔ A ∈ orbitOf O := by
  native_decide

/-- **Octatonic ground state (V-INDEPENDENT).** -/
theorem octatonic_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 8) :
    E V O ≤ E V A :=
  groundStateG O V hc0 hc1 hc2 hc3 hdec _ census_hsum_O census_DD_O A hA

/-- **Octatonic uniqueness (V-INDEPENDENT).** -/
theorem octatonic_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 8) :
    E V O = E V A ↔ A ∈ orbitOf O :=
  uniqueG O V hc0 hc1 hc2 hc3 hdec _ _ census_hsum_O census_DD_O census_offorbit_O
    census_onorbit_O A hA

/-! ### k = 6 — whole-tone `{0,2,4,6,8,10}` (orbit size 2, degenerate IV with zeros) -/

/-- `iv W = ⟨0,6,0,6,0,3⟩`. -/
theorem iv_W : iv W 1 = 0 ∧ iv W 2 = 6 ∧ iv W 3 = 0 ∧ iv W 4 = 6 ∧ iv W 5 = 0 ∧ iv W 6 = 3 := by
  decide

theorem census_hsum_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6,
    dg W A 0 + dg W A 1 + dg W A 2 + dg W A 3 + dg W A 4 + dg W A 5 = 0 := by
  native_decide

theorem census_DD_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6,
    0 ≤ DD (dg W A) 0 ∧ 0 ≤ DD (dg W A) 1 ∧ 0 ≤ DD (dg W A) 2 ∧ 0 ≤ DD (dg W A) 3
      ∧ 0 ≤ DD (dg W A) 4 := by
  native_decide

theorem census_offorbit_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6, A ∉ orbitOf W →
    0 < DD (dg W A) 0 ∨ 0 < DD (dg W A) 1 ∨ 0 < DD (dg W A) 2 ∨ 0 < DD (dg W A) 3
      ∨ 0 < DD (dg W A) 4 := by
  native_decide

theorem census_onorbit_W : ∀ A ∈ orbitOf W,
    iv A 1 = iv W 1 ∧ iv A 2 = iv W 2 ∧ iv A 3 = iv W 3 ∧ iv A 4 = iv W 4 ∧ iv A 5 = iv W 5
      ∧ iv A 6 = iv W 6 := by
  native_decide

/-- Single-V anchor: `E₀ W = 207` and `E₀ A = 207 ⟺ A ∈ orbit` over all 6-subsets. -/
theorem item1_min_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6, 207 ≤ E0 A := by
  native_decide

theorem item1_unique_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6,
    E0 A = 207 ↔ A ∈ orbitOf W := by
  native_decide

/-- **Whole-tone ground state (V-INDEPENDENT).** -/
theorem wholetone_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 6) :
    E V W ≤ E V A :=
  groundStateG W V hc0 hc1 hc2 hc3 hdec _ census_hsum_W census_DD_W A hA

/-- **Whole-tone uniqueness (V-INDEPENDENT).** Despite the degenerate IV (three zero classes), the
    off-orbit census still yields a strictly positive double-cumulative, so strict uniqueness holds
    for every strictly convex, strictly decreasing `V`. -/
theorem wholetone_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 6) :
    E V W = E V A ↔ A ∈ orbitOf W :=
  uniqueG W V hc0 hc1 hc2 hc3 hdec _ _ census_hsum_W census_DD_W census_offorbit_W
    census_onorbit_W A hA

/-! ### Axiom audit -/

-- AXIOM-CLEAN core (Abel bridge layer): [propext, Classical.choice, Quot.sound]
#print axioms abel_bridge
#print axioms abel_nonneg
#print axioms abel_pos
-- Census/capstones additionally carry Lean.ofReduceBool (from native_decide):
#print axioms item1_min
#print axioms item1_unique
#print axioms diatonic_ground_state
#print axioms diatonic_unique
-- New cardinalities (same axiom profile; native_decide censuses):
#print axioms pentatonic_ground_state
#print axioms pentatonic_unique
#print axioms octatonic_ground_state
#print axioms octatonic_unique
#print axioms wholetone_ground_state
#print axioms wholetone_unique

end AllPairsEvenness
