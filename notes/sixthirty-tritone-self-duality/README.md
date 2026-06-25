# 🎹 A tritone-centered self-duality: the set class 6-30 and its order-12 neo-Riemannian dual

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20820961-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20820961)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](../../LICENSE)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean_4-Mathlib-2C2C2C)](https://leanprover.github.io/)

> Carles Marín (with Claude, Anthropic, as AI assistant). Zenodo DOI: [10.5281/zenodo.20820961](https://doi.org/10.5281/zenodo.20820961).
> Note #1 in the *Mathematics of Music* series (companions: Note #2, the phase taxonomy; Note #3, the Tonnetz spectrum).

A focused, machine-checked research note. Stravinsky's *Petrushka* chord stacks two major triads a
tritone apart; following that tritone into group theory, we show that over $\mathbb{Z}_{12}$ a
pitch-class set class has a simply-transitive reduced **dual** group exactly when its $T/I$-stabilizer is
normal — and among order-2 symmetries this singles out the tritone center $\{T_0,T_6\}$. The unique such
class is Forte **6-30** = (013679), the Petrushka set class: orbit 12, dual dihedral of order 12
($\cong D_6$). We prove the characterization, enumerate the phenomenon (OEIS A032239, asymmetric
bracelets), and **machine-check** in Lean 4 both the Crans–Fiore–Satyendra duality engine and 6-30's
order-12 regular dihedral dual.

## 📄 Files
- `sixthirty_note.pdf` / `.tex` — the note (English).
- `sixthirty_note_es.pdf` / `.tex` — Spanish version.

## 🔧 Reproducibility
- **Lean 4** (`../../lean/`): `NeoRiemannian.lean` (the duality engine, Brick 3) and `SixThirty.lean`
  (6-30's dual, Brick 19). Compile against Mathlib; every named theorem audits to
  `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. `SixThirty.lean` imports
  `NeoRiemannian` (compile `NeoRiemannian` first; both live in `../../lean/`).
- **Sage/GAP** (`../../sage/`): `centralizer_witness.sage`, `sixthirty.sage`, `duality_sweep.sage`,
  `sc630_verify.sage` — each re-runnable in Sage 10.8 + GAP, outputs quoted in the note.

## 🎯 Scope
Formalization + characterization, not new mathematics: the duality engine is the regular case of
Wielandt's centralizer theorem; the contribution is the tritone characterization (with proof), the 6-30
instance with its first machine-checked contextual dual, and the enumeration. The named isomorphism
$\cong D_6$ is GAP-witnessed (a current Mathlib gap); Lean proves order 12 + regular + the dihedral
fingerprint.
