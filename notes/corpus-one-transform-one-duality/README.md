# 🎼 One transform and one duality: a machine-checked core of music theory in Lean 4

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20953768-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20953768)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](../../LICENSE)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean_4-Mathlib-2C2C2C)](https://leanprover.github.io/)

> Carles Marín Muñoz (with Claude, Anthropic, as AI assistant). Zenodo DOI: [10.5281/zenodo.20953768](https://doi.org/10.5281/zenodo.20953768).
> The **corpus / Lean-library paper** of the *Mathematics of Music* series — the umbrella over Note #1
> (the 6-30 self-duality), Note #2 (the phase taxonomy) and Note #3 (the Tonnetz spectrum).

A machine-checked library, in Lean 4 on top of Mathlib, of core results in mathematical music theory over
the chromatic universe $\mathbb{Z}_{12}$, organized so that **one object and one phenomenon do most of the
work**. The object is the autocorrelation / power spectrum $|\hat A|^2$ of a pitch-class set: the interval
vector, Babbitt's hexachord theorem, homometry and the $Z$-relation (read as the crystallographic phase
problem), deep scales, rhythmic oddity and the common-tone theorems are functions of it, and maximal
evenness reconnects to it in the scale theory. The phenomenon is **duality**: the neo-Riemannian $PLR$
group is the centralizer of the regular $T/I$ action on the 24 triads (Crans–Fiore–Satyendra, via the
regular case of Wielandt's centralizer theorem, a lemma added over Mathlib), and the same shape recurs as
the tritone-centered order-12 self-duality of 6-30 and as the val–comma lattice duality of regular
temperament theory.

Three pillars (Fourier invariants · transformational duality · scales and tuning), ~275 theorems and
lemmas across 9 Lean files, every theorem `sorry`-free with a clean axiom audit.

## 📄 Files
- `corpus_paper.pdf` / `.tex` — the paper (English).
- `corpus_paper_es.pdf` / `.tex` — Spanish version.
- `pillar1_fourier.tex`, `pillar2_duality.tex`, `pillar3_scales_tuning.tex` (+ `_es`) — the pillar bodies,
  `\input` by the master.

## 🔧 Reproducibility
- **Lean 4** (`../../lean/`): `Fourier.lean`, `IntervalVector.lean`, `NeoRiemannian.lean`, `SixThirty.lean`,
  `DiatonicScale.lean`, `MaximalEvenness.lean`, `AllPairsEvenness.lean`, `Temperament.lean`,
  `CircleOfFifths.lean`. Compile against Mathlib; every named theorem audits to
  `[propext, Classical.choice, Quot.sound]` with no `sorryAx` (the finite maximal-evenness censuses in
  `AllPairsEvenness.lean` additionally use `native_decide`, adding `Lean.ofReduceBool`). Some files import
  others (`SixThirty`→`NeoRiemannian`, `CircleOfFifths`→`Temperament`), so build them as a package.
- **Sage/GAP** (`../../sage/`) and **audio** (`../../media/`) accompany the constituent notes.
- **Build the PDF:** `pdflatex corpus_paper.tex` (twice, for refs); the pillar files must sit alongside it.

## 🎯 Scope
Formalization + organization, **not new mathematics**. The mathematics is classical; the contributions are
the formalization itself (the first comprehensive one in this area — prior proof-assistant work covers only
the $T/I$ action), the autocorrelation/DFT organizing lens, and two items we believe are unstated in the
literature: the **6-30 self-duality** and a **unified phase taxonomy** of the $|\hat A|^2$ invariants.
Every scope and limitation statement is the author's; the Lean 4 kernel — not the assistant — certifies the
formalized parts.
