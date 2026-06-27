/- CircleOfFifths.lean — the cross-file bridge ℤ² → ℤ/12: why the circle of fifths closes.
   Author: Carles Marín  <karlesmarin@gmail.com>   (with Claude, Anthropic, as assistant)

   The FIRST genuine cross-file theorem of the music-math development: it imports BOTH the
   just-intonation lattice ℤ² of `Temperament.lean` (Brick 15, monzos/vals/commas) AND the chromatic
   pitch-class circle ℤ/12 of `DiatonicScale.lean` (Brick 13/14, generated scales `stack`). The
   12-EDO reduction `red : ℤ² → ℤ/12` sends a JI interval to its pitch class; under it the perfect
   fifth becomes the generator `7` that `stack` iterates, the octave becomes the unison `0`
   (octave equivalence), and the Pythagorean comma — the closure defect of twelve stacked fifths
   (`closure_defect_eq_pc`) and the generator of `ker v12` (`ker_v12_eq_span_pc`) — vanishes to `0`.
   The payoff `circle_of_fifths_complete : stack 0 (red fifth) 12 = univ` is the precise statement that
   the comma lying in the 12-EDO kernel is *why* the ℤ/12 circle of fifths both CLOSES and is COMPLETE.

   Scope/honesty: first FORMALIZATION, NOT new math. It welds two already-GREEN bricks; the content is
   the reduction homomorphism + the literal "tempered comma ⇒ pitch-class unison" link. Establishes
   that our standalone files CAN cross-import (re-tested 2026-06-23 — the old "needs a lake package"
   assumption was wrong; `--root` + `LEAN_PATH` suffices), which also retires the Fourier.lean / IVraw
   duplication rationale.

   Multi-file build (deps first, then this file with LEAN_PATH), from godsil-gutman-lean env:
     MM=…/research/music-math/lean
     lake env lean --root="$MM" -o "$MM/DiatonicScale.olean" "$MM/DiatonicScale.lean"
     lake env lean --root="$MM" -o "$MM/Temperament.olean"   "$MM/Temperament.lean"
     LEAN_PATH="$MM;$LEAN_PATH" lake env lean --root="$MM" "$MM/CircleOfFifths.lean" -/
import DiatonicScale
import Temperament

namespace CircleOfFifths

open DiatonicScale Temperament

/-- **The 12-EDO reduction.** A just-intonation monzo `2^a·3^b` ↦ its pitch class in ℤ/12, i.e. the
    val's step count taken mod 12. Concretely `red (a,b) = (12a + 19b : ℤ/12) = 7·b` (since `12 ≡ 0`,
    `19 ≡ 7`). This is the homomorphism that maps the JI lattice onto the chromatic circle. -/
def red (m : ℤ × ℤ) : ZMod 12 := ((v12 m : ℤ) : ZMod 12)

/-- The octave is the pitch-class unison: `red oct = 0` (octave equivalence). -/
theorem red_oct : red oct = 0 := by unfold red; simp [oct]; decide

/-- **The perfect fifth reduces to the generator `7`** — exactly the generator `stack` iterates in
    `DiatonicScale.lean`. This is the seam between the two files. -/
theorem red_fifth : red fifth = 7 := by unfold red; simp [fifth]

/-- **The Pythagorean comma vanishes in ℤ/12:** `red pc = 0`. The closure defect of the circle of
    fifths is the pitch-class unison — the comma is "tempered out" literally, not just to a small number. -/
theorem red_pc : red pc = 0 := by unfold red; simp [pc]

/-- **Any comma tempered by 12-EDO is a pitch-class unison.** `red` factors through `v12`, so every
    element of `ker v12` reduces to `0` — the formal content of "tempering out a comma". -/
theorem red_kernel_vanishes (m : ℤ × ℤ) (h : m ∈ LinearMap.ker v12) : red m = 0 := by
  rw [LinearMap.mem_ker] at h
  unfold red; rw [h]; simp

/-- The closure defect of the circle of fifths reduces to the unison: `red (12•fifth − 7•oct) = 0`.
    (From `closure_defect_eq_pc` then `red_pc`.) -/
theorem red_closure_defect : red ((12 : ℤ) • fifth - (7 : ℤ) • oct) = 0 := by
  rw [closure_defect_eq_pc]; exact red_pc

/-- **THE BRIDGE THEOREM.** Stacking the perfect fifth twelve times on the chromatic circle — with the
    generator being exactly `red fifth` from the JI lattice — visits *every* pitch class:
    `stack 0 (red fifth) 12 = univ`. The circle of fifths CLOSES (returns to `0` after twelve steps)
    and is COMPLETE (hits all twelve notes). This is the cross-file reason `ker_v12_eq_span_pc` /
    `closure_defect_eq_pc` (in ℤ²) force the ℤ/12 circle to close: the comma lands in the kernel ⇒
    `red` collapses the defect to `0`. -/
theorem circle_of_fifths_complete : stack 0 (red fifth) 12 = Finset.univ := by
  rw [red_fifth, Finset.ext_iff]; decide

/-! ### §meantone — the ℤ/12 face of the meantone identity: four fifths = a major third

  The 5-limit analog of the circle-of-fifths bridge. The 12-EDO reduction `red5 : ℤ³ → ℤ/12` sends the
  just major third 5/4 to the pitch class `4` and the perfect fifth to `7`; four fifths reduce to
  `4·7 = 28 ≡ 4 (mod 12)`, the same `4`. So in 12-EDO four perfect fifths (mod octaves) ARE a major
  third — the harmonic seed of triadic functional harmony, and the ℤ/12 shadow of
  `Temperament.meantone_identity_tempered`. First FORMALIZATION, not new math. -/

/-- **The 5-limit 12-EDO reduction.** A 5-limit monzo `2^a·3^b·5^c` ↦ its pitch class in ℤ/12, i.e. the
    5-limit val `v12_5` taken mod 12. Mirrors `red` on the 3-limit lattice. -/
def red5 (m : ℤ × ℤ × ℤ) : ZMod 12 := ((v12_5 m : ℤ) : ZMod 12)

/-- The perfect fifth reduces to `7`. -/
theorem red5_fifth5 : red5 fifth5 = 7 := by unfold red5; simp [fifth5]

/-- The just major third 5/4 reduces to the pitch class `4`. -/
theorem red5_third5 : red5 third5 = 4 := by unfold red5; simp [third5]

/-- The octave reduces to the pitch-class unison `0` (octave equivalence). -/
theorem red5_oct5 : red5 oct5 = 0 := by unfold red5; simp [oct5]; decide

/-- **In 12-EDO, four fifths up equal a major third (mod octaves):** `red5 (4•fifth5) = red5 third5`.
    Both sides are the pitch class `4` (`4·7 = 28 ≡ 4`). This is the harmonic analog of
    `circle_of_fifths_complete` and the ℤ/12 face of `meantone_identity_tempered`. -/
theorem four_fifths_eq_major_third : red5 ((4 : ℤ) • fifth5) = red5 third5 := by
  rw [red5_third5]; unfold red5; simp [fifth5]; decide

end CircleOfFifths

-- Axiom audit (expect: [propext, Classical.choice, Quot.sound] or cleaner, no sorryAx).
#print axioms CircleOfFifths.red_oct
#print axioms CircleOfFifths.red_fifth
#print axioms CircleOfFifths.red_pc
#print axioms CircleOfFifths.red_kernel_vanishes
#print axioms CircleOfFifths.red_closure_defect
#print axioms CircleOfFifths.circle_of_fifths_complete
#print axioms CircleOfFifths.red5_fifth5
#print axioms CircleOfFifths.red5_third5
#print axioms CircleOfFifths.red5_oct5
#print axioms CircleOfFifths.four_fifths_eq_major_third
