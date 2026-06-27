/- DiatonicScale.lean — Myhill's property of the diatonic scale (§L.5).
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   Formalizes §L.5 of FORMULAS.md: a scale has **Myhill's property** (MP) when every nonzero GENERIC
   interval comes in exactly two SPECIFIC sizes. We give the first formalization (textbook fact, NOT new
   math) of the canonical instance: the diatonic scale {0,2,4,5,7,9,11} ⊂ ℤ/12 has MP.

   Conventions (matched to the literature — Harasim–Schmidt–Rohrmeier 2020; Carey–Clampitt 1989;
   Clough–Myerson 1985):
   • generic interval = a step-count `k` on the cyclically ordered `n`-note scale (`Fin n`); the
     nonzero generics are `k = 1 … n-1` (the octave `k ≡ 0` is excluded).
   • specific size of generic `k` at position `i` = the circular semitone gap `s(i+k) − s(i)` in ℤ/12.
   • **MP is `card = 2` EXACTLY** (two distinct specific sizes). The weaker `card ≤ 2` is *maximal
     evenness* (ME), NOT MP — do not conflate. Non-degeneracy (generator coprime to 12) is exactly what
     rules out the `card = 1` case: the whole-tone scale is ME but NOT MP (`wholeTone_not_hasMyhill`).

   Scope: first FORMALIZATION of a known instance. The general theorem MP ⟺ non-degenerate well-formed
   (Carey–Clampitt 1989; simplified proof Harasim et al. 2020) needs Christoffel/three-gap word machinery
   (§C.3/C.5, thin in Mathlib) and is an open multi-session campaign, NOT this brick.

   Fast-loop build: lake env lean DiatonicScale.lean (from godsil-gutman env). -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases

namespace DiatonicScale

variable {n : ℕ} [NeZero n]

/-- The **specific size** of the generic interval `k` measured at scale degree `i`: the circular
    semitone gap `s(i+k) − s(i)` in ℤ/12 (index `i+k` taken mod `n`, the cyclic scale order). -/
def specSize (s : Fin n → ZMod 12) (k i : Fin n) : ZMod 12 := s (i + k) - s i

/-- The **spectrum** of a generic interval `k`: the set of specific sizes it takes across all degrees. -/
def genericSpectrum (s : Fin n → ZMod 12) (k : Fin n) : Finset (ZMod 12) :=
  Finset.image (specSize s k) Finset.univ

/-- **Myhill's property.** Every nonzero generic interval has exactly two distinct specific sizes.
    (`= 2` is MP; `≤ 2` would be maximal evenness — a strictly weaker property.) -/
def HasMyhill (s : Fin n → ZMod 12) : Prop :=
  ∀ k : Fin n, k ≠ 0 → (genericSpectrum s k).card = 2

/-- The diatonic scale (C major) as the cyclically ordered 7-tuple of pitch classes. -/
def diatonic : Fin 7 → ZMod 12 := ![0, 2, 4, 5, 7, 9, 11]

/-- The whole-tone scale: maximally even but degenerate (generator `2`, `gcd(2,12)=2`). -/
def wholeTone : Fin 6 → ZMod 12 := ![0, 2, 4, 6, 8, 10]

/-- **§L.5 — the diatonic scale has Myhill's property** (first formalization; Carey–Clampitt 1989). -/
theorem diatonic_hasMyhill : HasMyhill diatonic := by unfold HasMyhill; decide

/-- The whole-tone scale does **not** have MP: every generic interval has a single specific size
    (it is maximally even but degenerate). This separates MP from ME. -/
theorem wholeTone_not_hasMyhill : ¬ HasMyhill wholeTone := by unfold HasMyhill; decide

/-- The seven diatonic spectra, witnessed: each nonzero generic interval splits into exactly two
    specific sizes — and the tritone `6` lives as the second size of the generic fourth and fifth. -/
example : genericSpectrum diatonic 1 = {1, 2} := by decide   -- generic 2nd: minor/major
example : genericSpectrum diatonic 2 = {3, 4} := by decide   -- generic 3rd: minor/major
example : genericSpectrum diatonic 3 = {5, 6} := by decide   -- generic 4th: perfect/augmented (tritone)
example : genericSpectrum diatonic 4 = {6, 7} := by decide   -- generic 5th: diminished (tritone)/perfect
example : genericSpectrum diatonic 5 = {8, 9} := by decide   -- generic 6th: minor/major
example : genericSpectrum diatonic 6 = {10, 11} := by decide -- generic 7th: minor/major

/-- Whole-tone witness: the generic step has a single specific size `{2}` (card 1, not 2). -/
example : genericSpectrum wholeTone 1 = {2} := by decide

/-! ### §L (ME) — Maximal evenness (Clough–Douthett), and how it differs from Myhill -/

/-- Specific sizes of generic interval `k` as integers `0…11` (lifted from `ZMod 12` by `val`),
    so "consecutive" is honest integer adjacency (no modular wrap ambiguity). -/
def specSizesNat (s : Fin n → ZMod 12) (k : Fin n) : Finset ℕ :=
  (genericSpectrum s k).image ZMod.val

/-- **Maximal evenness.** Every nonzero generic interval takes at most two specific sizes, and those
    are **consecutive integers**. Strictly weaker than Myhill (which demands *exactly* two): a
    maximally even scale may have a generic interval of a single size — that is the ME∖MP gap. -/
def IsMaxEven (s : Fin n → ZMod 12) : Prop :=
  ∀ k : Fin n, k ≠ 0 →
    (specSizesNat s k).card ≤ 2 ∧
      ∀ a ∈ specSizesNat s k, ∀ b ∈ specSizesNat s k, b ≤ a + 1

/-- **§L.ME — the diatonic scale is maximally even** (Clough–Douthett; first formalization). It is
    therefore in the ME ∩ MP intersection (`diatonic_hasMyhill` + this) — the source of its specialness. -/
theorem diatonic_isMaxEven : IsMaxEven diatonic := by unfold IsMaxEven; decide

/-- The whole-tone scale **is** maximally even — yet `wholeTone_not_hasMyhill` shows it is not Myhill.
    Together they witness **ME ⊋ MP** as a theorem (whole-tone ∈ ME ∖ MP). -/
theorem wholeTone_isMaxEven : IsMaxEven wholeTone := by unfold IsMaxEven; decide

/-! ### §C.4 — Generated scales: well-formedness's generator side (Carey–Clampitt)

A scale is *well-formed* when generated by a single interval. We record the canonical generator
instances over ℤ/12 as decidable set equalities (first formalization of the textbook facts). -/

/-- The pitch-class set of `d` consecutive copies of the generator `g` starting at `start`:
    `{start, start+g, …, start+(d−1)g}`. The starting point selects the KEY/mode; the *set* is the
    generated scale. Defined as a `filter` over `univ` (not `image`) so equalities reduce under `decide`. -/
def stack (start g : ZMod 12) (d : ℕ) : Finset (ZMod 12) :=
  Finset.univ.filter (fun x => ∃ k : Fin d, start + g * (k.val : ZMod 12) = x)

/-- **The diatonic scale is generated by the perfect fifth** — seven CONSECUTIVE fifths
    (F C G D A E B, i.e. starting at the subdominant `5`) give exactly C major `{0,2,4,5,7,9,11}`.
    The generator characterization at the heart of well-formedness (Carey–Clampitt). -/
theorem diatonic_generated_by_fifth : stack 5 7 7 = {0, 2, 4, 5, 7, 9, 11} := by
  rw [Finset.ext_iff]; decide

/-- The pitch-class set of the `diatonic` tuple (Brick 11) is exactly that stack of seven fifths. -/
theorem diatonic_range_eq_stack : Finset.univ.image diatonic = stack 5 7 7 := by
  rw [Finset.ext_iff]; decide

/-- Stacking fifths from a different start just transposes: from `0` the seven fifths give G major
    `{0,2,4,6,7,9,11}` — same set class, different key. -/
theorem stack_fifths_from_zero : stack 0 7 7 = {0, 2, 4, 6, 7, 9, 11} := by
  rw [Finset.ext_iff]; decide

/-- **The major pentatonic is generated by the fifth** too (five stacked fifths from `0`): `{0,2,4,7,9}`. -/
theorem pentatonic_generated_by_fifth : stack 0 7 5 = {0, 2, 4, 7, 9} := by
  rw [Finset.ext_iff]; decide

/-! ### §C.5 — The three-gap (Steinhaus) theorem, discrete ℤ/12 form

The **three-gap theorem** (Steinhaus, conjectured 1950s; proved by Sós, Świerczkowski, Surányi):
for points `{0, g, 2g, …, (d−1)g}` on a circle, the gaps between cyclically adjacent points take **at
most three distinct sizes**. We formalize its *discrete* incarnation on the fixed chromatic circle ℤ/12,
where the statement becomes DECIDABLE — no continued-fraction machinery is needed because the universe
is finite. This is the **first Lean formalization** of the theorem (a general/continuous version exists
in Coq — Mayero et al.), and additionally the first formalization of its music-theoretic reading: a
GENERATED scale has ≤ 3 step sizes, and is **well-formed** exactly when it has *2* step sizes
(Carey–Clampitt 1989; Clough–Myerson 1985). Not new math — first formalization.

This is the FINITE half toward the open §L.5 MP ⟺ WF campaign; general WF ⟺ Christoffel remains a
multi-session campaign, NOT discharged here. -/

/-- The **cyclic successor gap** of a pitch-class set `S` at `x`: the smallest positive `δ ∈ 1…12`
    with `x + δ ∈ S` (the semitone distance from `x` to the next note of `S` going up the circle).
    Defined by a bounded `List.find?` search so it reduces under `decide`. If `S` is empty above `x`
    in `1…12` it returns `12` (a full octave); for nonempty `S` containing `x`, `δ ≤ 12` always hits. -/
def succGap (S : Finset (ZMod 12)) (x : ZMod 12) : ℕ :=
  (((List.range 12).find? (fun δ => x + ((δ + 1 : ℕ) : ZMod 12) ∈ S)).getD 11) + 1

/-- The **step sizes** (adjacent gaps) of a pitch-class set: the set of successor gaps over its notes.
    For a scale, these are the semitone sizes of its consecutive steps (e.g. diatonic = whole & half). -/
def stepSizes (S : Finset (ZMod 12)) : Finset ℕ :=
  S.image (succGap S)

/-- **§C.5 — the three-gap theorem on the chromatic circle.** For EVERY generator `g : ZMod 12` and
    EVERY count `d ≤ 12`, the generated set `{0, g, 2g, …, (d−1)g}` has at most three distinct step
    sizes. Proved by exhausting `d` (`interval_cases`) and deciding the finite `∀ g`. Full ∀-scope:
    no narrowing — all 12 generators, all 13 values `d = 0…12`. -/
theorem threeGap_chromatic :
    ∀ (g : ZMod 12) (d : ℕ), d ≤ 12 → (stepSizes (stack 0 g d)).card ≤ 3 := by
  intro g d hd
  interval_cases d <;> revert g <;> decide

/-- **Two-step-size property (MOS), the floor of the three-gap bound.** A pitch-class set has exactly
    *two* step sizes — Wilson's "moment of symmetry". ⚠ For a single-generator (GENERATED) scale this is
    exactly Carey–Clampitt **well-formedness**, which is how we use it below (every witness is a `stack`).
    As a bare set predicate it is STRICTLY BROADER than well-formed: e.g. the octatonic `{0,1,3,4,6,7,9,10}`
    has two step sizes `{1,2}` yet is not single-generated (ℤ/12 has no order-8 element) — MOS but not WF.
    Do not read `IsWellFormed S` as "S is well-formed" for arbitrary `S`; read it as "S is MOS". -/
def IsWellFormed (S : Finset (ZMod 12)) : Prop := (stepSizes S).card = 2

/-- The diatonic scale (seven fifths) is **well-formed**: exactly two step sizes, `{1, 2}` — the
    semitone and the whole tone. (The three-gap bound is *attained at its floor*: 2 < 3.) -/
theorem diatonic_isWellFormed : IsWellFormed (stack 5 7 7) := by
  unfold IsWellFormed; decide

/-- The diatonic step sizes are precisely `{1, 2}` (half step and whole step). -/
theorem diatonic_stepSizes : stepSizes (stack 5 7 7) = {1, 2} := by decide

/-- The major pentatonic (five fifths) is **well-formed** too: two step sizes `{2, 3}` — the whole
    tone and the minor third. -/
theorem pentatonic_isWellFormed : IsWellFormed (stack 0 7 5) := by
  unfold IsWellFormed; decide

/-- Pentatonic step sizes are precisely `{2, 3}`. -/
theorem pentatonic_stepSizes : stepSizes (stack 0 7 5) = {2, 3} := by decide

/-- **The load-bearing witness that "3" is achieved.** Six stacked fifths `{0,2,4,7,9,11}` give a
    scale with **exactly three** step sizes `{1, 2, 3}` — the three-gap bound is SATURATED, and the
    scale is NOT well-formed. This is the proper-third-gap case the theorem's `≤ 3` allows. -/
theorem sixFifths_stepSizes : stepSizes (stack 0 7 6) = {1, 2, 3} := by decide

/-- Six fifths: three step sizes, and therefore NOT well-formed (`card = 3 ≠ 2`). -/
theorem sixFifths_not_wellFormed : ¬ IsWellFormed (stack 0 7 6) := by
  unfold IsWellFormed; decide

/-- A second saturating witness via a different generator: six stacked perfect FOURTHS (`g = 5`)
    `{0,1,3,5,8,10}` also hit exactly three step sizes `{1, 2, 3}`. Confirms the bound's saturation is
    not an artifact of the fifth. -/
theorem sixFourths_stepSizes : stepSizes (stack 0 5 6) = {1, 2, 3} := by decide

/-- Six fourths: not well-formed either (three step sizes). -/
theorem sixFourths_not_wellFormed : ¬ IsWellFormed (stack 0 5 6) := by
  unfold IsWellFormed; decide

end DiatonicScale

-- Axiom audit (expect: [propext, Classical.choice, Quot.sound] or cleaner, no sorryAx).
#print axioms DiatonicScale.diatonic_hasMyhill
#print axioms DiatonicScale.wholeTone_not_hasMyhill
#print axioms DiatonicScale.diatonic_isMaxEven
#print axioms DiatonicScale.wholeTone_isMaxEven
#print axioms DiatonicScale.diatonic_generated_by_fifth
#print axioms DiatonicScale.diatonic_range_eq_stack
#print axioms DiatonicScale.stack_fifths_from_zero
#print axioms DiatonicScale.pentatonic_generated_by_fifth
#print axioms DiatonicScale.threeGap_chromatic
#print axioms DiatonicScale.diatonic_isWellFormed
#print axioms DiatonicScale.diatonic_stepSizes
#print axioms DiatonicScale.pentatonic_isWellFormed
#print axioms DiatonicScale.pentatonic_stepSizes
#print axioms DiatonicScale.sixFifths_stepSizes
#print axioms DiatonicScale.sixFifths_not_wellFormed
#print axioms DiatonicScale.sixFourths_stepSizes
#print axioms DiatonicScale.sixFourths_not_wellFormed
