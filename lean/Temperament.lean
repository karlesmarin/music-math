/- Temperament.lean — the comma-kernel bridge: regular temperament theory over ℤ (§J / RTT).
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   Formalizes the algebraic skeleton of Regular Temperament Theory (RTT) in the 3-limit (primes 2, 3),
   so the monzo lattice is ℤ × ℤ (exponents of 2 and 3). A `val` is a ℤ-linear functional
   `ℤ² →ₗ[ℤ] ℤ` (steps-per-prime of an EDO); a `comma` is an element of its kernel (an interval the
   temperament treats as a unison). We prove: (1) the BRIDGE to Brick 13/14 — twelve stacked perfect
   fifths minus seven octaves equals the Pythagorean comma (the closure defect of the circle of fifths);
   (2) 12-EDO tempers the Pythagorean comma; (3) the comma GENERATES the whole kernel of the 12-EDO val
   (ker v12 = span_ℤ{pc}, the one nontrivial proof — a Bézout/coprimality argument); (4) neither 5-EDO
   nor 7-EDO tempers it (so 12 is special). 5-limit coda: 12-EDO is a meantone (tempers the syntonic comma).

   Scope/honesty: this is the first FORMALIZATION of RTT's DEFINITIONS (monzo/val/comma) plus a specific
   kernel computation — NOT new mathematics. Mathlib supplies ℤ-modules, `LinearMap.ker`, `Submodule.span`;
   RTT is established (Smith; Erlich; Xenharmonic wiki; Flieder 2025, J. Math. Music). The only nontrivial
   content is the Bézout direction of theorem 3. The VALUE is UNIFICATION: `closure_defect_eq_pc` is exactly
   why the ℤ/12 circle of fifths in DiatonicScale.lean (Brick 13/14) closes — the comma lands in the 12-EDO
   kernel. RTT is val ⊣ comma lattice duality, the same flavor as our PLR/centralizer Lewin duality, here
   over ℤ-modules.

   Fast-loop build: lake env lean Temperament.lean (from godsil-gutman env). -/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

namespace Temperament

/-! ### Monzos: the 3-limit just-intonation lattice ℤ × ℤ -/

/-- The **perfect fifth** 3/2, as a monzo `(exp of 2, exp of 3) = (-1, 1)`. -/
def fifth : ℤ × ℤ := (-1, 1)

/-- The **octave** 2/1, as a monzo `(1, 0)`. -/
def oct : ℤ × ℤ := (1, 0)

/-- The **Pythagorean comma** `3^12 / 2^19 = 531441/524288`, as a monzo `(-19, 12)`. -/
def pc : ℤ × ℤ := (-19, 12)

/-! ### Vals: ℤ-linear "steps per prime" functionals -/

/-- The **12-EDO patent val** `⟨12, 19|`: a perfect octave is 12 steps, a perfect twelfth (`3/1`) is 19
    steps, so `2^a·3^b ↦ 12a + 19b`. -/
def v12 : ℤ × ℤ →ₗ[ℤ] ℤ where
  toFun p := 12 * p.1 + 19 * p.2
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c p := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    RingHom.id_apply]; ring

/-- The **5-EDO val** `⟨5, 8|`. -/
def v5 : ℤ × ℤ →ₗ[ℤ] ℤ where
  toFun p := 5 * p.1 + 8 * p.2
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c p := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    RingHom.id_apply]; ring

/-- The **7-EDO val** `⟨7, 11|`. -/
def v7 : ℤ × ℤ →ₗ[ℤ] ℤ where
  toFun p := 7 * p.1 + 11 * p.2
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c p := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    RingHom.id_apply]; ring

@[simp] theorem v12_apply (p : ℤ × ℤ) : v12 p = 12 * p.1 + 19 * p.2 := rfl
@[simp] theorem v5_apply  (p : ℤ × ℤ) : v5 p  = 5 * p.1 + 8 * p.2  := rfl
@[simp] theorem v7_apply  (p : ℤ × ℤ) : v7 p  = 7 * p.1 + 11 * p.2 := rfl

/-! ### Theorem 1 — the bridge: the comma is the closure defect of the circle of fifths -/

/-- **Twelve stacked fifths minus seven octaves equals the Pythagorean comma.** This is the closure
    defect of the circle of fifths and the bridge to DiatonicScale.lean (Brick 13/14): it is exactly
    why stacking the fifth twelve times in ℤ/12 returns to the start (the defect lands in the kernel of
    the 12-EDO val — see `closure_defect_tempered`). -/
theorem closure_defect_eq_pc : (12 : ℤ) • fifth - (7 : ℤ) • oct = pc := by
  decide

/-! ### Theorem 2 — 12-EDO tempers the Pythagorean comma -/

/-- **12-EDO tempers out the Pythagorean comma:** `v12 pc = 12·(-19) + 19·12 = 0`. -/
theorem v12_tempers_pc : v12 pc = 0 := by
  simp [pc]

/-- Corollary phrased on the closure defect itself: the defect of the circle of fifths is a comma of
    12-EDO. This is the precise reason the ℤ/12 circle of fifths closes. -/
theorem closure_defect_tempered : v12 ((12 : ℤ) • fifth - (7 : ℤ) • oct) = 0 := by
  rw [closure_defect_eq_pc]; exact v12_tempers_pc

/-! ### Theorem 3 — the comma generates the kernel (the only nontrivial proof) -/

/-- **The Pythagorean comma generates the entire kernel of the 12-EDO val:**
    `ker v12 = span_ℤ {pc}`. The `⊇` direction is `span_le` + theorem 2. The `⊆` direction is the
    Bézout content: if `12a + 19b = 0` then, reducing `19 ≡ 7 (mod 12)` and using `gcd(7,12)=1`,
    we get `12 ∣ b`; writing `b = 12t` forces `a = -19t`, i.e. `(a,b) = t • pc`. -/
theorem ker_v12_eq_span_pc : LinearMap.ker v12 = Submodule.span ℤ {pc} := by
  apply le_antisymm
  · -- ⊆ : the Bézout direction
    intro p hp
    rw [LinearMap.mem_ker, v12_apply] at hp
    obtain ⟨a, b⟩ := p
    simp only at hp           -- hp : 12 * a + 19 * b = 0
    rw [Submodule.mem_span_singleton]
    -- 12 ∣ b : from 12*a + 19*b = 0 and 19 = 12 + 7, omega handles the divisibility witness.
    refine ⟨b / 12, ?_⟩
    have h12b : (12 : ℤ) ∣ b := by omega
    obtain ⟨t, rfl⟩ := h12b
    -- now hp : 12 * a + 19 * (12 * t) = 0  ⇒  a = -19 * t
    have ha : a = -19 * t := by omega
    simp only [pc, Prod.smul_mk, smul_eq_mul]
    -- goal: (12 * t / 12) • (-19, 12) = (a, 12 * t)
    have hdiv : (12 : ℤ) * t / 12 = t := by omega
    rw [hdiv]
    exact Prod.ext (by simp [ha]; ring) (by ring)
  · -- ⊇ : span ⊆ ker
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact v12_tempers_pc

/-! ### Theorem 4 — 5-EDO and 7-EDO do NOT temper the comma -/

/-- **5-EDO does not temper the Pythagorean comma:** `v5 pc = 1 ≠ 0`. -/
theorem v5_pc : v5 pc = 1 := by simp [pc]

/-- **7-EDO does not temper the Pythagorean comma:** `v7 pc = -1 ≠ 0`. -/
theorem v7_pc : v7 pc = -1 := by simp [pc]

/-- Restated: 12 is special among 5, 7, 12 — only 12-EDO sends the comma to a unison. -/
theorem only_twelve_tempers_pc : v12 pc = 0 ∧ v5 pc ≠ 0 ∧ v7 pc ≠ 0 :=
  ⟨v12_tempers_pc, by rw [v5_pc]; decide, by rw [v7_pc]; decide⟩

/-! ### 5-limit coda — 12-EDO is a meantone (tempers the syntonic comma) -/

/-- The **12-EDO val in the 5-limit** `⟨12, 19, 28|` on the monzo lattice ℤ × ℤ × ℤ (primes 2, 3, 5). -/
def v12_5 : ℤ × ℤ × ℤ →ₗ[ℤ] ℤ where
  toFun p := 12 * p.1 + 19 * p.2.1 + 28 * p.2.2
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem v12_5_apply (p : ℤ × ℤ × ℤ) :
    v12_5 p = 12 * p.1 + 19 * p.2.1 + 28 * p.2.2 := rfl

/-- The **syntonic comma** `81/80 = 3^4·5⁻¹·2⁻⁴`, as a 5-limit monzo `(-4, 4, -1)`. -/
def syntonic : ℤ × ℤ × ℤ := (-4, 4, -1)

/-- **12-EDO is a meantone:** it tempers out the syntonic comma,
    `12·(-4) + 19·4 + 28·(-1) = 0`. -/
theorem v12_5_tempers_syntonic : v12_5 syntonic = 0 := by simp [syntonic]

/-! ### The rank-2 kernel: the two classical commas GENERATE the 5-limit comma lattice

  Brick 18. The honest completion of the 5-limit kernel picture. Where B15 gave the rank-1
  3-limit fact `ker v12 = span_ℤ{pc}`, here the kernel of the 5-limit val is rank 2, and the two
  classical commas — the syntonic comma `81/80` AND the Pythagorean comma `3¹²/2¹⁹` (embedded in
  the 5-limit, no factor of 5) — TOGETHER generate the whole sublattice of commas 12-EDO tempers
  out. They genuinely GENERATE (not merely lie in) the kernel because the gcd of the 2×2 minors of
  the matrix `[syntonic; pc5]` is `gcd(28, −19, 12) = 1`, so `{syntonic, pc5}` is a ℤ-basis of the
  saturated rank-2 kernel. First FORMALIZATION, NOT new math. -/

/-- The **Pythagorean comma embedded in the 5-limit** `3¹²/2¹⁹` (no factor of 5),
    as a 5-limit monzo `(-19, 12, 0)`. -/
def pc5 : ℤ × ℤ × ℤ := (-19, 12, 0)

/-- **12-EDO tempers the (5-limit) Pythagorean comma:** `12·(-19) + 19·12 + 28·0 = 0`. -/
theorem v12_5_tempers_pc5 : v12_5 pc5 = 0 := by simp [pc5]

/-- **The syntonic and Pythagorean commas generate the entire 5-limit kernel of the 12-EDO val:**
    `ker v12_5 = span_ℤ {syntonic, pc5}`. This is a genuine rank-2 lattice-generation theorem. The
    `⊇` direction is `span_le` + the two tempering facts. The `⊆` direction is a 2D-Bézout content
    made omega-checkable by explicit witnesses: any tempered comma `(a,b,c)` with `12a+19b+28c=0`
    equals `(-c)•syntonic + t•pc5` where `12t = b+4c` (the divisibility `12 ∣ b+4c` follows from the
    kernel equation mod 12). The witnesses exist because the 2×2-minor gcd is 1 (saturated kernel). -/
theorem ker_v12_5_eq_span : LinearMap.ker v12_5 = Submodule.span ℤ {syntonic, pc5} := by
  apply le_antisymm
  · -- ⊆ : any tempered comma is a ℤ-combination of syntonic and pc5
    intro m hm
    rw [LinearMap.mem_ker, v12_5_apply] at hm
    obtain ⟨a, b, c⟩ := m
    simp only at hm        -- hm : 12 * a + 19 * b + 28 * c = 0
    rw [Submodule.mem_span_pair]
    have hdvd : (12 : ℤ) ∣ (b + 4 * c) := by omega
    obtain ⟨t, ht⟩ := hdvd   -- ht : b + 4 * c = 12 * t
    refine ⟨-c, t, ?_⟩
    simp only [syntonic, pc5, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> · simp only []; omega
  · -- ⊇ : both generators lie in the kernel
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩ <;>
      rw [SetLike.mem_coe, LinearMap.mem_ker, v12_5_apply]
    · simp [syntonic]
    · simp [pc5]

/-! ### Meantone identity — the syntonic comma is "four fifths vs. a major third"

  The defining identity of meantone temperament (Aron 1523; textbook 5-limit RTT): four perfect
  fifths, reduced by two octaves, exceed the *just* major third (5/4) by exactly the syntonic comma.
  Tempering the comma (which 12-EDO does, `v12_5_tempers_syntonic`) makes the identity exact, which is
  *why* a stack of four fifths lands on a major third in any meantone. This is the SECOND great comma
  of the kernel wing (syntonic, after the Pythagorean `pc`), and the algebraic seed of triadic harmony.
  First FORMALIZATION, not new math. -/

/-- The **perfect fifth** 3/2 as a 5-limit monzo `(-1, 1, 0)`. -/
def fifth5 : ℤ × ℤ × ℤ := (-1, 1, 0)

/-- The **octave** 2/1 as a 5-limit monzo `(1, 0, 0)`. -/
def oct5 : ℤ × ℤ × ℤ := (1, 0, 0)

/-- The **just major third** 5/4 as a 5-limit monzo `(-2, 0, 1)`. -/
def third5 : ℤ × ℤ × ℤ := (-2, 0, 1)

/-- **The meantone defect is the syntonic comma:** four perfect fifths minus a just major third minus
    two octaves equals `81/80`. `4•(-1,1,0) − (-2,0,1) − 2•(1,0,0) = (-4,4,-1) = syntonic`. This is the
    gap between four fifths and a (just) major third plus two octaves. -/
theorem meantone_defect_eq_syntonic :
    (4 : ℤ) • fifth5 - third5 - (2 : ℤ) • oct5 = syntonic := by
  decide

/-- **12-EDO closes the meantone identity:** it tempers the four-fifths-vs-major-third defect to a
    unison. Hence in 12-EDO four fifths (mod octaves) *are* a major third — the harmonic analog of the
    circle of fifths closing. -/
theorem meantone_identity_tempered :
    v12_5 ((4 : ℤ) • fifth5 - third5 - (2 : ℤ) • oct5) = 0 := by
  rw [meantone_defect_eq_syntonic]; exact v12_5_tempers_syntonic

end Temperament

-- Axiom audit (expect: [propext, Classical.choice, Quot.sound] or cleaner, no sorryAx).
#print axioms Temperament.closure_defect_eq_pc
#print axioms Temperament.v12_tempers_pc
#print axioms Temperament.closure_defect_tempered
#print axioms Temperament.ker_v12_eq_span_pc
#print axioms Temperament.v5_pc
#print axioms Temperament.v7_pc
#print axioms Temperament.only_twelve_tempers_pc
#print axioms Temperament.v12_5_tempers_syntonic
#print axioms Temperament.v12_5_tempers_pc5
#print axioms Temperament.ker_v12_5_eq_span
#print axioms Temperament.meantone_defect_eq_syntonic
#print axioms Temperament.meantone_identity_tempered
