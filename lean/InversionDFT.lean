/- InversionDFT.lean — the dihedral group D₁₂ = ⟨T, I⟩ acts BLOCK-DIAGONALLY in the DFT basis:
   translation is diagonal, inversion swaps `dftChar k ↔ dftChar (-k)`, so every
   `span{dftChar k, dftChar (-k)}` is a D₁₂-invariant 2-dimensional block.
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   THE MUSIC. Pitch classes ℤ/12 carry two transformations dear to neo-Riemannian and
   transformational theory: TRANSPOSITION `T_a` (shift every note up by `a` semitones) and
   INVERSION `I` (flip the chromatic circle, n ↦ -n). Together they generate the dihedral
   group D₁₂ — the T/I group acting on chords. Lewin/Quinn's "Fourier balances" `a_k = dft Φ k`
   live in the DFT basis `{dftChar k}`, where harmony's shift-invariant structure is diagonal.
   This brick asks: how do T and I act on that Fourier basis? The answer is the reason the
   "generative ℂ[D₁₂]" program collapses to the ordinary abelian pitch-class DFT: D₁₂ does NOT
   mix all 12 characters freely — it only ever pairs `k` with `-k`. Non-abelian Fourier over D₁₂
   reduces to the abelian pc-DFT QUOTIENTED BY INVERSION.

   THE MATH. With `dftChar k j = stdAddChar (j*k) = exp(2πi·jk/N)`:
     • TRANSLATION `transl a Φ x = Φ (x - a)` acts diagonally:
         transl a (dftChar k) = stdAddChar(-(a·k)) • dftChar k.
       Because `(x-a)·k = x·k + (-(a·k))` and `stdAddChar` is an `AddChar` (`map_add_eq_mul`),
       this is the same one-line split as the R.1 circulant diagonalization `hsplit`.
     • INVERSION `inv Φ x = Φ (-x)` swaps the characters:
         inv (dftChar k) = dftChar (-k),
       since `(-x)·k = x·(-k)`.
   Hence the 2-dim block `block k = span{dftChar k, dftChar (-k)}` is mapped into itself by both
   `inv` (it permutes the two generators, using `-(-k) = k`) and every `transl a` (each generator
   ↦ scalar·itself). That is the block-diagonalization of the D₁₂ action. Over ℤ/12 the self-paired
   classes `{k | k = -k} = {0, 6}` give the two 1-dim blocks, and the five pairs {1,11},…,{5,7}
   give five 2-dim blocks: `2·1 + 5·2 = 12 = dim ℂ[ℤ₁₂]`.

   Mathlib already has the Φ-level statement `ZMod.dft_comp_neg` (inversion ↔ k ↦ -k under `dft`);
   we work one level down, directly on the characters `dftChar`, re-deriving in a line each.

   SCOPE / honesty. First FORMALIZATION of the inversion-block structure of the D₁₂ action on
   ℂ[ℤ₁₂] via the DFT basis. The mathematics is standard representation theory — the ±k pairing
   of dihedral irreducibles (Amiot, Luo own the music-theoretic use); NOT new mathematics. The
   value is a machine-checked account of WHY ℂ[D₁₂]-Fourier collapses to the abelian pc-DFT.
   R.2 next-layer (added): each 2-dim block is IRREDUCIBLE for k ∉ {0,6} (`block_irreducible`,
   via eigenvalue separation). Documented frontier still NOT attempted: the named isomorphism to
   the abstract D₁₂ irreps / isotypic `DirectSum` (Mathlib has no dihedral-irrep classification).

   KNOWN DEBT. `dftChar`/`stdAddChar` are re-declared locally (≤ a few lines) to keep this file
   self-contained and avoid cross-import build-order fragility with CycleGraphSpectrum.lean (same
   `dftChar`). De-dup is future cleanup, same status as the B16 note.

   Lives over ℂ (noncomputable, propositional — NOT the decidable idiom; T3 alone uses `decide`
   over ZMod 12). Sorry-free, axiom-clean (`#print axioms` at the foot of the file).

   Fast-loop build: lake env lean InversionDFT.lean (from godsil-gutman env). -/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

open Complex Real

namespace InversionDFT

open ZMod AddChar

variable {N : ℕ} [NeZero N]

/-- The k-th DFT character as a vector on `ZMod N`: `dftChar k j = stdAddChar (j * k)`.
    (Local copy of `CycleGraphSpectrum.dftChar`; see KNOWN DEBT in the header.) -/
noncomputable def dftChar (k : ZMod N) : ZMod N → ℂ := fun j => stdAddChar (j * k)

@[simp] lemma dftChar_apply (k j : ZMod N) : dftChar k j = stdAddChar (j * k) := rfl

/-! ### T1 — the two operator actions on the DFT basis. -/

/-- Pitch-class INVERSION operator: `inv Φ x = Φ (-x)` (flip the chromatic circle). -/
noncomputable def inv (Φ : ZMod N → ℂ) : ZMod N → ℂ := fun x => Φ (-x)

/-- TRANSPOSITION operator by `a` semitones: `transl a Φ x = Φ (x - a)`. -/
noncomputable def transl (a : ZMod N) (Φ : ZMod N → ℂ) : ZMod N → ℂ := fun x => Φ (x - a)

/-- **Inversion swaps `k ↔ -k` (T1).** `inv (dftChar k) = dftChar (-k)`: inversion permutes the
    DFT characters by negating the frequency. -/
theorem inv_dftChar (k : ZMod N) : inv (dftChar k) = dftChar (-k) := by
  funext x
  simp only [inv, dftChar_apply, neg_mul, mul_neg]

/-- **Translation is diagonal (T1).** `transl a (dftChar k) = stdAddChar (-(a*k)) • dftChar k`:
    each DFT character is an eigenvector of every transposition, with eigenvalue the root of
    unity `stdAddChar(-(a·k))`. Same `AddChar` split as the R.1 circulant `hsplit`. -/
theorem transl_dftChar (a k : ZMod N) :
    transl a (dftChar k) = stdAddChar (-(a * k)) • dftChar k := by
  funext x
  simp only [transl, dftChar_apply, Pi.smul_apply, smul_eq_mul]
  -- (x - a)*k = x*k + (-(a*k)); split the character
  rw [sub_mul, sub_eq_add_neg, map_add_eq_mul]
  ring

/-! ### T2 — the D₁₂-invariant 2-dimensional block. -/

/-- The 2-dim block `block k = span{dftChar k, dftChar (-k)}` — a D₁₂-invariant subspace. -/
noncomputable def block (k : ZMod N) : Submodule ℂ (ZMod N → ℂ) :=
  Submodule.span ℂ {dftChar k, dftChar (-k)}

/-- Both generators of `block k` lie in `block k` (trivially); recorded for the membership proofs. -/
lemma dftChar_mem_block (k : ZMod N) : dftChar k ∈ block k :=
  Submodule.subset_span (by simp)

lemma dftChar_neg_mem_block (k : ZMod N) : dftChar (-k) ∈ block k :=
  Submodule.subset_span (by simp)

/-- **Inversion preserves the block (T2).** `inv` maps `block k` into `block k`: it swaps the two
    spanning characters (`dftChar k ↦ dftChar (-k)` and `dftChar (-k) ↦ dftChar k`, using
    `-(-k) = k`), so the whole span is preserved. -/
theorem inv_mem_block (k : ZMod N) {Φ : ZMod N → ℂ} (hΦ : Φ ∈ block k) :
    inv Φ ∈ block k := by
  -- `inv` is ℂ-linear; induct over the span generators.
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with h | h
      · -- x = dftChar k  ↦  dftChar (-k)
        subst h; rw [inv_dftChar]; exact dftChar_neg_mem_block k
      · -- x = dftChar (-k)  ↦  dftChar k   (since -(-k) = k)
        rw [Set.mem_singleton_iff] at h
        subst h; rw [inv_dftChar, neg_neg]; exact dftChar_mem_block k
  | zero =>
      have : inv (0 : ZMod N → ℂ) = 0 := by funext z; simp [inv]
      rw [this]; exact Submodule.zero_mem (block k)
  | add x y _ _ hx hy =>
      have : inv (x + y) = inv x + inv y := by funext z; simp [inv]
      rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      have : inv (c • x) = c • inv x := by funext z; simp [inv]
      rw [this]; exact Submodule.smul_mem _ c hx

/-- **Translation preserves the block (T2).** Every transposition `transl a` maps `block k` into
    `block k`: each generator goes to a scalar times itself, hence stays in the span. -/
theorem transl_mem_block (a k : ZMod N) {Φ : ZMod N → ℂ} (hΦ : Φ ∈ block k) :
    transl a Φ ∈ block k := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with h | h
      · subst h; rw [transl_dftChar]
        exact Submodule.smul_mem _ _ (dftChar_mem_block k)
      · rw [Set.mem_singleton_iff] at h
        subst h; rw [transl_dftChar]
        exact Submodule.smul_mem _ _ (dftChar_neg_mem_block k)
  | zero =>
      have : transl a (0 : ZMod N → ℂ) = 0 := by funext z; simp [transl]
      rw [this]; exact Submodule.zero_mem (block k)
  | add x y _ _ hx hy =>
      have : transl a (x + y) = transl a x + transl a y := by funext z; simp [transl]
      rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      have : transl a (c • x) = c • transl a x := by funext z; simp [transl]
      rw [this]; exact Submodule.smul_mem _ c hx

/-- **The block is D₁₂-invariant (T2 corollary).** `block k` is closed under inversion AND under
    every transposition `transl a` — i.e. under the whole group ⟨T, I⟩ = D₁₂. This is the
    block-diagonalization of the dihedral action in the DFT basis. -/
theorem block_dihedral_invariant (k : ZMod N) {Φ : ZMod N → ℂ} (hΦ : Φ ∈ block k) :
    inv Φ ∈ block k ∧ ∀ a : ZMod N, transl a Φ ∈ block k :=
  ⟨inv_mem_block k hΦ, fun a => transl_mem_block a k hΦ⟩

/-! ### T3 — the pairing counts over ℤ/12.

The self-paired classes `{k | k = -k}` are exactly `{0, 6}`: the two 1-dim blocks. The remaining
ten classes split into the five pairs {1,11},{2,10},{3,9},{4,8},{5,7}, each a 2-dim block. The
dimension bookkeeping `2·1 + 5·2 = 12 = dim ℂ[ℤ₁₂]` is recorded as an `example`. -/

/-- **The self-paired classes over ℤ/12 (T3).** `{k : ZMod 12 | k = -k} = {0, 6}`: exactly the two
    frequencies fixed by inversion, giving the two 1-dimensional blocks. (`decide` over ZMod 12.) -/
theorem selfPaired_eq : {k : ZMod 12 | k = -k} = {0, 6} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert k
  decide

/-- Dimension bookkeeping: 2 one-dim blocks (k ∈ {0,6}) + 5 two-dim blocks (the ±k pairs)
    account for all of `dim ℂ[ℤ₁₂] = 12`. -/
example : 2 * 1 + 5 * 2 = 12 := by norm_num

/-! ### C-1 — the dihedral block census for ALL N (R.2 generalized off the n=12 instance).

`selfPaired_eq` and the `2·1 + 5·2 = 12` bookkeeping above are the EVEN instance of a statement true
over every `ZMod N`. The self-paired frequencies `{k | k = -k}` — the negation fixed points = the
1-dimensional dihedral blocks — and the rest pair into 2-dimensional blocks:
  • N ODD  : self-paired `= {0}`        (1 one-dim block ; (N−1)/2 two-dim blocks),
  • N EVEN : self-paired `= {0, N/2}`   (2 one-dim blocks; (N−2)/2 two-dim blocks — the extra
                                          self-paired frequency is the TRITONE `N/2`).
The count of 1-dim blocks is `gcd(2, N)`. The structural theorems above (`block_dihedral_invariant`,
`block_irreducible`) are ALREADY proved for arbitrary `N`; only this census was pinned to 12. So R.2
holds for every universe, not just the chromatic one. Engine: Mathlib's `ZMod.neg_eq_self_iff`. -/

omit [NeZero N] in
/-- **Self-paired ⟺ negation fixed point (C-1).** `k = -k ↔ k = 0 ∨ 2 * k.val = N`: a frequency is its
    own inverse exactly at the DC term, or where `2·k = N` (the tritone, available only for even N). -/
theorem selfPaired_iff (k : ZMod N) : k = -k ↔ (k = 0 ∨ 2 * k.val = N) := by
  constructor
  · intro h; exact (ZMod.neg_eq_self_iff k).mp h.symm
  · intro h; exact ((ZMod.neg_eq_self_iff k).mpr h).symm

omit [NeZero N] in
/-- **Odd N — one 1-dim block (C-1).** `{k : ZMod N | k = -k} = {0}`: for odd N the equation
    `2·k.val = N` is even = odd, impossible, so inversion fixes only the DC frequency. -/
theorem selfPaired_odd (hodd : Odd N) : {k : ZMod N | k = -k} = {0} := by
  obtain ⟨j, hj⟩ := hodd
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, selfPaired_iff]
  constructor
  · rintro (h | h)
    · exact h
    · omega
  · rintro rfl; exact Or.inl rfl

/-- **Even N — two 1-dim blocks, DC and the TRITONE (C-1).** `{k : ZMod N | k = -k} = {0, (m : ZMod N)}`
    where `N = 2m`: the only nonzero self-paired frequency is the tritone `m = N/2`. The n=12 case
    `{0, 6}` (`selfPaired_eq`) is `m = 6`. -/
theorem selfPaired_even (m : ℕ) (hm : N = 2 * m) :
    {k : ZMod N | k = -k} = {0, (m : ZMod N)} := by
  have hmlt : m < N := by have := NeZero.pos N; omega
  have hval : ((m : ZMod N)).val = m := ZMod.val_cast_of_lt hmlt
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, selfPaired_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ?_
      have hkv : k.val = m := by omega
      calc k = ((k.val : ℕ) : ZMod N) := (ZMod.natCast_zmod_val k).symm
        _ = ((m : ℕ) : ZMod N) := by rw [hkv]
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by rw [hval]; omega)

/-- **The tritone is self-paired in every even universe (C-1, the music payload).** `(m : ZMod N) =
    -(m : ZMod N)` when `N = 2m`: the tritone `N/2` is fixed by inversion in every even `ℤ_N`. This is
    the structural reason the tritone keeps recurring (6-30 center, O.1 doubling, O.3 parity split). -/
theorem tritone_selfPaired (m : ℕ) (hm : N = 2 * m) : (m : ZMod N) = -(m : ZMod N) := by
  rw [selfPaired_iff]
  exact Or.inr (by rw [ZMod.val_cast_of_lt (by have := NeZero.pos N; omega : m < N)]; omega)

omit [NeZero N] in
/-- **One 1-dim block for odd N (C-1, count).** `gcd(2,N) = 1`: inversion has a single fixed frequency. -/
theorem selfPaired_ncard_odd (hodd : Odd N) : ({k : ZMod N | k = -k}).ncard = 1 := by
  rw [selfPaired_odd hodd, Set.ncard_singleton]

/-- **Two 1-dim blocks for even N (C-1, count).** `gcd(2,N) = 2`: inversion fixes exactly the DC term
    and the tritone. -/
theorem selfPaired_ncard_even (m : ℕ) (hm : N = 2 * m) :
    ({k : ZMod N | k = -k}).ncard = 2 := by
  have hmlt : m < N := by have := NeZero.pos N; omega
  have hm1 : 1 ≤ m := by have := NeZero.pos N; omega
  have hne : (0 : ZMod N) ≠ (m : ZMod N) := by
    intro h
    have hv : ((m : ZMod N)).val = m := ZMod.val_cast_of_lt hmlt
    have h0 : ((m : ZMod N)).val = 0 := by rw [← h]; simp
    omega
  rw [selfPaired_even m hm, Set.ncard_pair hne]

/-- Dimension bookkeeping for all N (C-1): `(#1-dim)·1 + (#2-dim)·2 = N` — odd `1 + 2·(N−1)/2 = N`,
    even `2 + 2·(N−2)/2 = N`. (n=12 is the even case `2 + 2·5 = 12`.) -/
example (j : ℕ) : 1 + 2 * j = 2 * j + 1 := by omega
example (m : ℕ) (hm : 1 ≤ m) : 2 * 1 + 2 * (m - 1) = 2 * m := by omega

/-! ### [C-D] — the conjugate pair `{k, −k}` as ONE object (the cross-engine spine).

The frequency and its inversion-image always travel together. The three generative engines
(prospector, cartographer, Sócrates) all converged on the SAME vertebra: the conjugate pair
`conjPair k = {k, −k}` — the orbit of `k` under negation — is the single object behind every place
the tritone "keeps showing up":
  • R.2 block index : `block k` is exactly the span of `dftChar '' conjPair k` (`block_eq_span_conjPair`);
    the block DIMENSION is `(conjPair k).ncard` ∈ {1, 2} — 1 at the self-paired `{0, N/2}`, else 2.
  • C-1 census      : self-paired `k = -k ⟺ conjPair k` is a singleton (`conjPair_ncard_*`); the
    even-universe singleton at `N/2` is `tritone_selfPaired`.
  • CROSS-FILE (documented, welded at de-dup): the IV-fold `ivc_fibre` (Fourier.lean) fibres the index
    over `conjPair`; O.3's parity marginal splits along the self-paired `{0, N/2}` = the singleton pairs;
    the 6-30 self-dual center is `conjPair 0 ∪ conjPair 6` collapsing. One object, every appearance. -/

/-- The conjugate pair / negation orbit `conjPair k = {k, −k}` — the R.2 block index. -/
def conjPair (k : ZMod N) : Set (ZMod N) := {k, -k}

omit [NeZero N] in
@[simp] theorem mem_conjPair {k j : ZMod N} : j ∈ conjPair k ↔ j = k ∨ j = -k := Iff.rfl

omit [NeZero N] in
/-- **The pair is well-defined on the negation quotient ([C-D]).** `conjPair (-k) = conjPair k`: the
    two ends of a conjugate pair name the same object — `conjPair` factors through `k ~ -k`. -/
theorem conjPair_neg (k : ZMod N) : conjPair (-k) = conjPair k := by
  unfold conjPair; rw [neg_neg, Set.pair_comm]

/-- **The R.2 block is the span of the conjugate pair ([C-D], ties to R.2).** `block k = span ℂ
    (dftChar '' conjPair k)`: the dihedral block is literally the span of the two characters indexed by
    the conjugate pair. So `conjPair k` IS the block index. -/
theorem block_eq_span_conjPair (k : ZMod N) :
    block k = Submodule.span ℂ (dftChar '' conjPair k) := by
  unfold block conjPair; rw [Set.image_pair]

omit [NeZero N] in
/-- **Self-paired ⟹ the block is 1-dimensional ([C-D]).** When `k = -k` the conjugate pair collapses to
    a singleton, `(conjPair k).ncard = 1`: the two fixed frequencies `{0, N/2}` are the 1-dim blocks. -/
theorem conjPair_ncard_of_selfPaired {k : ZMod N} (h : k = -k) : (conjPair k).ncard = 1 := by
  unfold conjPair; rw [← h, Set.pair_eq_singleton, Set.ncard_singleton]

omit [NeZero N] in
/-- **Not self-paired ⟹ the block is 2-dimensional ([C-D]).** When `k ≠ -k` the conjugate pair has two
    elements, `(conjPair k).ncard = 2`: the genuine 2-dim irreducible blocks. -/
theorem conjPair_ncard_of_not {k : ZMod N} (h : k ≠ -k) : (conjPair k).ncard = 2 :=
  Set.ncard_pair h

/-- **The tritone pair is a singleton in every even universe ([C-D] × C-1).** `conjPair (N/2)` collapses
    to `{N/2}` for `N = 2m`: the tritone is its own conjugate, so its block is 1-dimensional. The single
    object unifying `tritone_selfPaired`, the 6-30 center, the O.1 doubling, the O.3 parity split. -/
theorem conjPair_tritone_ncard (m : ℕ) (hm : N = 2 * m) : (conjPair (m : ZMod N)).ncard = 1 :=
  conjPair_ncard_of_selfPaired (tritone_selfPaired m hm)

/-! ### R.2 next-layer — IRREDUCIBILITY of the 2-dim blocks (eigenvalue separation).

For `k ≠ -k` the block `block k` is an IRREDUCIBLE ⟨T, I⟩ = D₁₂ representation: it has no proper
nonzero subspace invariant under both `inv` and all `transl a`. The mechanism is eigenvalue
separation — at `a = 1` the two `transl 1` eigenvalues `stdAddChar(-k)` and `stdAddChar k` are
DISTINCT iff `k ≠ -k`, so the only `transl`-invariant lines are the two coordinate axes, which `inv`
swaps. Standard 2-dim-dihedral-irrep representation theory; first formalization for this concrete
DFT block. -/

/-! #### T-next-1 — eigenvalue apartness. -/

/-- **Eigenvalue apartness (T-next-1).** For `k ≠ -k` the two `transl 1` eigenvalues are distinct:
    `stdAddChar k ≠ stdAddChar (-k)`. Immediate from injectivity of the standard additive character
    (`ZMod.injective_stdAddChar`). -/
theorem dftChar_apart {k : ZMod N} (hk : k ≠ -k) : stdAddChar k ≠ stdAddChar (-k) :=
  fun h => hk (injective_stdAddChar h)

/-- **The non-self-paired ℤ/12 frequencies (T-next-1, ZMod face).** Over ℤ/12, `k ∉ {0,6}` is
    exactly the apartness hypothesis `k ≠ -k` (contrapositive of `selfPaired_eq`). -/
theorem not_selfPaired {k : ZMod 12} (hk : k ∉ ({0, 6} : Set (ZMod 12))) : k ≠ -k := by
  intro h
  exact hk (by rw [← selfPaired_eq]; exact h)

/-! #### T-next-2 — pair independence + operator linearity. -/

omit [NeZero N] in
/-- `transl a` is additive. -/
theorem transl_add (a : ZMod N) (Φ Ψ : ZMod N → ℂ) :
    transl a (Φ + Ψ) = transl a Φ + transl a Ψ := by funext z; simp [transl]

omit [NeZero N] in
/-- `transl a` is ℂ-homogeneous. -/
theorem transl_smul (a : ZMod N) (c : ℂ) (Φ : ZMod N → ℂ) :
    transl a (c • Φ) = c • transl a Φ := by funext z; simp [transl]

omit [NeZero N] in
/-- `inv` is additive. -/
theorem inv_add (Φ Ψ : ZMod N → ℂ) : inv (Φ + Ψ) = inv Φ + inv Ψ := by
  funext z; simp [inv]

omit [NeZero N] in
/-- `inv` is ℂ-homogeneous. -/
theorem inv_smul (c : ℂ) (Φ : ZMod N → ℂ) : inv (c • Φ) = c • inv Φ := by
  funext z; simp [inv]

/-- `dftChar k 0 = 1`. -/
@[simp] lemma dftChar_zero (k : ZMod N) : dftChar k 0 = 1 := by
  simp [dftChar, AddChar.map_zero_eq_one]

/-- `dftChar k 1 = stdAddChar k`. -/
@[simp] lemma dftChar_one (k : ZMod N) : dftChar k 1 = stdAddChar k := by
  simp [dftChar]

/-- **Pair independence (T-next-2).** For `k ≠ -k` the two DFT characters `dftChar k`, `dftChar (-k)`
    are ℂ-linearly independent: a vanishing combination `c • dftChar k + d • dftChar (-k) = 0` forces
    `c = d = 0`. Proof: evaluate at `x = 0` (gives `c + d = 0`) and at `x = 1` (gives
    `c·stdAddChar k + d·stdAddChar(-k) = 0`); the 2×2 system has determinant
    `stdAddChar(-k) − stdAddChar k ≠ 0` by `dftChar_apart`. -/
theorem dftChar_pair_indep {k : ZMod N} (hk : k ≠ -k) (c d : ℂ)
    (h : c • dftChar k + d • dftChar (-k) = 0) : c = 0 ∧ d = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dftChar_zero, dftChar_one,
    Pi.zero_apply, mul_one] at h0 h1
  -- h0 : c + d = 0,  h1 : c * stdAddChar k + d * stdAddChar (-k) = 0
  have hd : d = -c := by linear_combination h0
  subst hd
  -- h1 : c * stdAddChar k + (-c) * stdAddChar (-k) = 0
  have hc : c * (stdAddChar k - stdAddChar (-k)) = 0 := by linear_combination h1
  have hne : stdAddChar k - stdAddChar (-k) ≠ 0 := sub_ne_zero.mpr (dftChar_apart hk)
  have : c = 0 := by
    rcases mul_eq_zero.mp hc with hc0 | hc0
    · exact hc0
    · exact absurd hc0 hne
  exact ⟨this, by rw [this, neg_zero]⟩

/-! #### T-next-3 — concrete irreducibility (eigenvalue separation). -/

/-- Helper: the eigenvalue-separation vector. For `w₀ = c • dftChar k + d • dftChar (-k)`,
    `transl 1 w₀ - stdAddChar k • w₀ = (c * (stdAddChar (-k) - stdAddChar k)) • dftChar k`.
    The `dftChar (-k)` component cancels because `transl 1` acts on it by `stdAddChar k` — the same
    scalar we subtract. This is the algebra that isolates the `k`-eigenvector. -/
lemma eigen_sep (k : ZMod N) (c d : ℂ) :
    transl 1 (c • dftChar k + d • dftChar (-k)) - stdAddChar k • (c • dftChar k + d • dftChar (-k))
      = (c * (stdAddChar (-k) - stdAddChar k)) • dftChar k := by
  rw [transl_add, transl_smul, transl_smul, transl_dftChar, transl_dftChar]
  funext x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dftChar_apply,
    one_mul, neg_neg]
  ring

/-- **Concrete irreducibility of the 2-dim block (T-next-3, THE PRIZE).** For `k ≠ -k`, any subspace
    `W ≤ block k` invariant under inversion `inv` and all transpositions `transl a` is either `⊥` or
    all of `block k`. So `block k` is an IRREDUCIBLE ⟨T, I⟩ = D₁₂ representation. The proof is
    eigenvalue separation: a nonzero `w₀ ∈ W`, written `c • dftChar k + d • dftChar (-k)`, yields via
    `eigen_sep` the vector `u = c·(stdAddChar(-k) − stdAddChar k) • dftChar k ∈ W`; when `c ≠ 0` the
    scalar is nonzero (apartness) so `dftChar k ∈ W`, when `c = 0` then `dftChar (-k) ∈ W` directly;
    `inv` supplies the partner, hence `block k ≤ W`, and `le_antisymm` finishes. -/
theorem block_irreducible {k : ZMod N} (hk : k ≠ -k) (W : Submodule ℂ (ZMod N → ℂ))
    (hWle : W ≤ block k) (hinv : ∀ w ∈ W, inv w ∈ W)
    (htransl : ∀ (a : ZMod N) (w : ZMod N → ℂ), w ∈ W → transl a w ∈ W) :
    W = ⊥ ∨ W = block k := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · refine Or.inr ?_
    -- A nonzero witness in W, decomposed in the block basis.
    obtain ⟨w₀, hw₀W, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp (hWle hw₀W)
    -- Key claim: dftChar k ∈ W. Then inv gives dftChar (-k) ∈ W, hence block k ≤ W.
    have hchar_k : dftChar k ∈ W := by
      by_cases hc : c = 0
      · -- c = 0 ⇒ w₀ = d • dftChar (-k), with d ≠ 0; so dftChar (-k) ∈ W, then inv ⇒ dftChar k ∈ W.
        subst hc
        rw [zero_smul, zero_add] at hcd
        have hd : d ≠ 0 := by
          rintro rfl; rw [zero_smul] at hcd; exact hw₀ne hcd.symm
        have hcharneg : dftChar (-k) ∈ W := by
          have : dftChar (-k) = d⁻¹ • w₀ := by rw [← hcd, smul_smul, inv_mul_cancel₀ hd, one_smul]
          rw [this]; exact W.smul_mem _ hw₀W
        have := hinv _ hcharneg
        rwa [inv_dftChar, neg_neg] at this
      · -- c ≠ 0: extract via eigen_sep.
        have hu_mem : transl 1 w₀ - stdAddChar k • w₀ ∈ W :=
          W.sub_mem (htransl 1 w₀ hw₀W) (W.smul_mem _ hw₀W)
        rw [← hcd, eigen_sep] at hu_mem
        set γ : ℂ := c * (stdAddChar (-k) - stdAddChar k) with hγ
        have hγne : γ ≠ 0 := by
          rw [hγ]
          exact mul_ne_zero hc (sub_ne_zero.mpr (fun h => (dftChar_apart hk) h.symm))
        have : dftChar k = γ⁻¹ • (γ • dftChar k) := by
          rw [smul_smul, inv_mul_cancel₀ hγne, one_smul]
        rw [this]; exact W.smul_mem _ hu_mem
    have hchar_negk : dftChar (-k) ∈ W := by
      have := hinv _ hchar_k; rwa [inv_dftChar] at this
    -- block k ≤ W, then antisymmetry.
    refine le_antisymm hWle ?_
    rw [block, Submodule.span_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact hchar_k
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact hchar_negk

/-! ### DOCUMENTED FRONTIER (NOT attempted; Mathlib-thin for this concrete rep).
    DONE in the R.2 next-layer: IRREDUCIBILITY of each 2-dim `block k` for k ∉ {0,6} — that it has
    no proper nonzero ⟨T,I⟩-invariant subspace — is `block_irreducible` (concrete, via eigenvalue
    separation; this IS rigorous irreducibility).
    REMAINING frontier (deliberately out of scope):
      • Packaging as `IsSimpleModule` over `MonoidAlgebra ℂ (DihedralGroup 6)`.
      • The NAMED ISOMORPHISM `block k ≃ₗ[ℂ] (abstract D₁₂ irrep)` and the full isotypic
        decomposition `ℂ[ℤ₁₂] = ⊕ block` as a `DirectSum`/`Module.End` statement.
    Both need a dihedral-irrep CLASSIFICATION, which Mathlib lacks — heavy setup, next layer. -/

/-! ### MICROTONAL INSTANTIATION (#3) — the block census for arbitrary N-TET, for free.

    Every theorem above is generic over `{N : ℕ} [NeZero N]`, so the dihedral block decomposition holds
    in ANY equal temperament, instantiated with no extra proof. For the famous microtonal systems 19-, 31-,
    53-TET (all odd) the ONLY self-paired frequency is the DC term — there is NO tritone, and `gcd(2,N)=1`
    gives a single 1-dimensional block, the remaining `(N-1)/2` frequencies pairing into 2-dimensional
    irreducible blocks (`block_irreducible`, generic in N). For an even temperament such as 24-TET (quarter
    tones) the tritone reappears at `N/2 = 12`, giving two 1-dim blocks. The proof assistant supplies each
    instance by feeding `N` to the same generic theorem — no per-system work. -/

example : ({k : ZMod 19 | k = -k}).ncard = 1 := selfPaired_ncard_odd (by decide)   -- 19-TET: no tritone
example : ({k : ZMod 31 | k = -k}).ncard = 1 := selfPaired_ncard_odd (by decide)   -- 31-TET: no tritone
example : ({k : ZMod 53 | k = -k}).ncard = 1 := selfPaired_ncard_odd (by decide)   -- 53-TET: no tritone
example : ({k : ZMod 24 | k = -k}).ncard = 2 := selfPaired_ncard_even 12 (by decide) -- 24-TET: DC + tritone
example : (12 : ZMod 24) = -(12 : ZMod 24) := tritone_selfPaired 12 (by decide)      -- the 24-TET tritone

/-! ### Axiom audit. Every shipped theorem is `[propext, Classical.choice, Quot.sound]`-clean
    (no `sorryAx`, no custom axioms). -/

#print axioms inv_dftChar
#print axioms transl_dftChar
#print axioms dftChar_mem_block
#print axioms dftChar_neg_mem_block
#print axioms inv_mem_block
#print axioms transl_mem_block
#print axioms block_dihedral_invariant
#print axioms selfPaired_eq
#print axioms dftChar_apart
#print axioms not_selfPaired
#print axioms transl_add
#print axioms transl_smul
#print axioms inv_add
#print axioms inv_smul
#print axioms dftChar_zero
#print axioms dftChar_one
#print axioms dftChar_pair_indep
#print axioms eigen_sep
#print axioms block_irreducible
#print axioms selfPaired_iff
#print axioms selfPaired_odd
#print axioms selfPaired_even
#print axioms tritone_selfPaired
#print axioms selfPaired_ncard_odd
#print axioms selfPaired_ncard_even
#print axioms conjPair_neg
#print axioms block_eq_span_conjPair
#print axioms conjPair_ncard_of_selfPaired
#print axioms conjPair_ncard_of_not
#print axioms conjPair_tritone_ncard

end InversionDFT
