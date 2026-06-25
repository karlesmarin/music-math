# 🎼 Mathematics of Music — Machine-Checked Notes in Lean 4

[![Note 1 — DOI](https://img.shields.io/badge/Note_1-10.5281%2Fzenodo.20820961-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20820961)
[![Note 2 — DOI](https://img.shields.io/badge/Note_2-10.5281%2Fzenodo.20826773-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20826773)
[![Note 3 — DOI](https://img.shields.io/badge/Note_3-10.5281%2Fzenodo.20862821-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20862821)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](LICENSE)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean_4-Mathlib-2C2C2C)](https://leanprover.github.io/)
[![Source](https://img.shields.io/badge/source-karlesmarin%2Fmusic--math-1B6F8C?logo=github&logoColor=white)](https://github.com/karlesmarin/music-math)

A machine-checked formalization in **Lean 4 / Mathlib** of classical mathematical music theory — every
headline theorem `sorry`-free (`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`).
This is a **growing series** of focused, self-contained notes, each backed by a Lean formalization and
reproducible Sage/GAP witnesses, accreting toward a corpus / Lean-library paper and, eventually, a
constraint-search composition program built on the verified invariants. New notes are added under
`notes/` over time; each note also carries its own Zenodo DOI.

- 🎵 **Note 1 — *A tritone-centered self-duality***
  ([`sixthirty_note.pdf`](notes/sixthirty-tritone-self-duality/sixthirty_note.pdf) · EN;
  [ES](notes/sixthirty-tritone-self-duality/sixthirty_note_es.pdf)):
  Stravinsky's **Petrushka chord** is Forte set class **6-30** = (013679). Following its **tritone**
  into group theory, a pitch-class set class carries a simply-transitive **dual** group of reduced order
  (Lewin) exactly when its `T/I`-stabilizer is *normal* — and among order-2 symmetries this singles out
  the tritone center `{T₀,T₆}`. 6-30's orbit has size 12 and its dual is **dihedral of order 12** (`D₆`).
  The characterization is proved; the phenomenon is enumerated across universes (**OEIS A032239**,
  asymmetric bracelets); and both the Crans–Fiore–Satyendra duality engine and 6-30's order-12 regular
  dihedral dual are machine-checked. EN + ES, with MIDI/WAV sonifications. DOI (this note)
  [10.5281/zenodo.20820962](https://doi.org/10.5281/zenodo.20820962).

- 🎵 **Note 2 — *The phase taxonomy of pitch-class set invariants***
  ([`phase_taxonomy_note.pdf`](notes/phase-taxonomy-pitch-class-invariants/phase_taxonomy_note.pdf) · EN;
  [ES](notes/phase-taxonomy-pitch-class-invariants/phase_taxonomy_note_es.pdf)):
  Represent a pitch-class set by its `0/1` indicator and take its DFT `Â = |Â|e^{iφ}`. Every classical
  invariant sorts cleanly by **how much of the phase φ it retains**: the interval vector, Babbitt's
  hexachord theorem, homometry / the `Z`-relation, deep scales and common-tones-under-`T` are all
  functions of the phase-blind power spectrum `|Â|²` (= the autocorrelation = the crystallographic
  **Patterson function**); the inversion index vector keeps partial phase via `Â²`; the **bispectrum**
  (third order) is phase-blind yet resolves the `Z`-relation; the full `Â` is a complete invariant. The
  boundaries of this resolving-power ladder are machine-checked in `Fourier.lean`. DOI (this note)
  [10.5281/zenodo.20826774](https://doi.org/10.5281/zenodo.20826774).

- 🎵 **Note 3 — *The Tonnetz spectrum is the generating triad's Fourier balance profile***
  ([`spectral_note.pdf`](notes/fourier-spectra-pitch-symmetry/spectral_note.pdf) · EN;
  [ES](notes/fourier-spectra-pitch-symmetry/spectral_note_es.pdf)):
  The neo-Riemannian **Tonnetz** (the graph on the 24 major/minor triads joined by `P,L,R`) has an
  adjacency spectrum, and it is exactly **±the Fourier balances of the single triad that generates it** —
  `±{3, √5, √3, 1, 2cos(π/12), 2cos(5π/12)}`, the augmented `√5=|a₃|`, diminished `√3=|a₄|`, whole-tone
  `1=|a₆|`. One eigenbasis (the DFT) diagonalizes every translation-invariant operator, blocks the `T/I`
  group `D₂ₙ` into conjugate-pair irreducibles, and keys the non-abelian `PLR≅D₁₂` Cayley graph. The
  spectral formula is standard (Gao–Luo, with the Tonnetz as its `S={P,L,R}` instance); the contribution
  is the **musical reading** + a Lean certification that is *complete* (an explicit eigenvector basis, no
  irrep classification). An appendix extends the generative saturation rule to **24-EDO** (quarter tones),
  Sage-verified. EN + ES, with MIDI/WAV (incl. a microtonal realization). DOI (this note)
  [10.5281/zenodo.20862822](https://doi.org/10.5281/zenodo.20862822).

> **Notes 2 and 3 are both Fourier/spectral** and share `lean/Fourier.lean`: Note 2's homometry power
> spectrum `|Â|²` reappears in Note 3 as the conjugate-pair object behind the dihedral blocks (one
> `{k,−k}` quotient behind both notes).

## 🧩 What is formalized

### 🎹 Note 1 — the 6-30 / Petrushka tritone self-duality

Lean sources: `lean/NeoRiemannian.lean` (the duality engine) and `lean/SixThirty.lean` (6-30's dual).
All theorems below are `sorry`-free and axiom-clean (`#print axioms` = `propext, Classical.choice,
Quot.sound`).

| Theorem | Statement |
|---|---|
| `Duality.centralizing_fixedPoint_eq_one` | Wielandt regular case: in a faithful transitive action a centralizing perm fixing a point is `1` (a Mathlib gap-filler). |
| `Duality.centralizer_eq_PLR` | the Crans–Fiore–Satyendra duality `centralizer(T/I) = ⟨P,L,R⟩`; `card_PLRgrp = 24`. |
| `SixThirty.stab_T`, `orbit_card` | 6-30's `T/I`-stabilizer is `{T₀,T₆}`; orbit size 12; not inversionally symmetric. |
| `SixThirty.card_Cgrp` | the dual (centralizer on the orbit) has order `12`, built as the **opposite regular representation** (Mathlib has no centralizer-of-regular-rep result). |
| `SixThirty.Cgrp_transitive` | the dual acts transitively, hence regularly (simply transitive). |
| `SixThirty.dihedral_fingerprint` | order 12, an order-6 generator, an inverting involution — dihedral `D₆`. |

The reduced-duality characterization (with proof), the A032239 enumeration, and the Sage/GAP witnesses
are in the note. The *named* isomorphism `dual ≅ DihedralGroup 6` is GAP-witnessed (a current Mathlib
gap: `D₁₂/Z ≅ D₆`); Lean proves order 12 + regularity + the dihedral fingerprint.

### 🎶 Note 2 — the phase taxonomy of pitch-class invariants

Lean source: `Fourier.lean`. All `sorry`-free and axiom-clean. The note's ladder of increasing
resolving power, rung by rung:

| Theorem | Statement |
|---|---|
| `homometric_iff_powerSpec_eq` | the `Z`-relation ⟺ equal power spectrum `\|Â\|²` — the phase-blind floor. |
| `IVraw_eq_invDFT_power` | the interval vector is the inverse DFT of `\|Â\|²` (= the autocorrelation / Patterson function). |
| `hexachord_IVraw_eq_nat` | Babbitt's hexachord theorem: a hexachord and its complement share the interval vector (phase-blind). |
| `commonTonesInv_eq_sumcorr`, `sumcorr_eq_invDFT` | the inversion index vector is a function of `Â²` — partial phase only. |
| `carterPair_triple_distinct` | the bispectrum (triple correlation) is phase-blind yet **separates** the homometric Carter pair — third order resolves the `Z`-relation. |
| `Ahat_eq_iff` | the full `Â` (magnitude **and** phase) is a complete invariant — it determines the set exactly. |

The crystallographic crossing is rigorous, not analogy: autocorrelation = Patterson function, `|Â|²` = X-ray
diffraction intensity, the `Z`-relation = the phase problem. The contribution is the unified taxonomy with
its boundaries machine-checked — a first formalization, not new mathematics.

### 🎼 Note 3 — the Tonnetz spectrum as the triad's Fourier balances

Lean sources: `CycleGraphSpectrum.lean`, `InversionDFT.lean`, `Fourier.lean`, `TonnetzSpectrum.lean`,
`TonnetzCompleteness.lean`. All `sorry`-free and axiom-clean.

| Theorem | Statement |
|---|---|
| `circulant_mulVec_dftChar` | every circulant is diagonalized by the DFT characters; eigenvalue = `v̂(k)` (the keystone). |
| `C12_eigenvalue_cos` | the chromatic cycle `C₁₂` has spectrum `2cos(2πk/12)`. |
| `cayleyAdj_eigenvalue` | abelian Cayley spectrum = `∑_{s∈S} stdAddChar(−sk)` (Babai's character sum). |
| `block_dihedral_invariant`, `block_irreducible` | the `D₂ₙ` action is block-diagonal in the DFT basis; each 2-dim conjugate-pair block is irreducible. |
| `tritone_selfPaired` | the tritone is the inversion-fixed frequency in every even universe. |
| `A_mulVec_golden`, `A_mulVec_j4/j2/j1/j5` | the full irrational Tonnetz spectrum `√5,√3,1,2cos(π/12),2cos(5π/12)` by explicit eigenvectors. |
| `tonnetz_spectrum_complete_unconditional` | the 24 eigenvectors form a **basis** — completeness, no Sage, no irrep classification. |

Lean certifies completeness as the abstract basis (spectrum = `{±|1̂_T(k)|}`); the identification with the
named factored characteristic polynomial and its multiplicities is the exact Sage witness
(`sage/tonnetz_cayley_spectrum.py`). The microtonal `sage/z24_saturation.sage` verifies the 24-EDO
saturation table by exact cyclotomic arithmetic.

## 🗂️ Repository layout

```
notes/   — one folder per note: PDF (EN + ES), LaTeX source, per-note README
  ├── sixthirty-tritone-self-duality/        — Note 1 (6-30 / Petrushka tritone self-duality)
  ├── phase-taxonomy-pitch-class-invariants/ — Note 2 (the phase taxonomy)
  └── fourier-spectra-pitch-symmetry/        — Note 3 (the Tonnetz spectrum)
lean/    — Lean 4 sources (NeoRiemannian, SixThirty, Fourier,
           CycleGraphSpectrum, InversionDFT, TonnetzSpectrum, TonnetzCompleteness)
sage/    — Sage/GAP witness scripts, each re-runnable
media/   — audio companions (MIDI + WAV) and the generators make_audio*.py
viz/     — figure scripts (gear train, CRT torus, dyadic solenoid)
```

## 🔧 Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`
(`leanprover/lean4:v4.30.0-rc2`); Mathlib is pinned in `lakefile.lean`.

```bash
lake exe cache get      # prebuilt Mathlib oleans (recommended)
lake build              # all notes: NeoRiemannian, SixThirty, Fourier,
                        # CycleGraphSpectrum, InversionDFT, TonnetzSpectrum, TonnetzCompleteness
```

Axiom footprint — one headline theorem per note:

```lean
import SixThirty; import Fourier; import TonnetzSpectrum; import TonnetzCompleteness
#print axioms SixThirty.dihedral_fingerprint           -- Note 1: 6-30's dual is dihedral D₆
#print axioms Ahat_eq_iff                              -- Note 2: the full Â is a complete invariant
#print axioms tonnetz_spectrum_complete_unconditional  -- Note 3: the Tonnetz spectrum is complete
-- each: propext, Classical.choice, Quot.sound
```

## 🔊 Audio and numerical cross-checks

The notes' claims can be **heard** (`media/`, MIDI + WAV): Note 1 — the Petrushka chord, the `T₆`
invariance, a traversal of all twelve forms; Note 2 — the homometric `Z`-pair the bispectrum separates
(`inversion_4z15`, `inversion_4z29`, `z_pair`); Note 3 — the augmented `a₃` cycle, the Tonnetz hexatonic
walk, and a 24-EDO microtonal realization (`microtonal_z24`). And **re-verified** (`sage/`, Sage 10.8 +
GAP): the order-12 `D₆` dual and the A032239 counts (Note 1), the exact Tonnetz characteristic polynomial
and the `ℤ₂₄` saturation table (Note 3).

## 📚 Citing

Cite the specific note you use; each `doi` below is the **concept DOI** (always resolves to the latest
version).

```bibtex
@misc{Marin2026SixThirty,
  author = {Mar\'in, Carles},
  title  = {A Tritone-Centered Self-Duality: the Set Class 6-30 and its Order-12 Neo-Riemannian Dual},
  year   = {2026}, doi = {10.5281/zenodo.20820961},
  note   = {Note 1, Mathematics of Music series. \url{https://github.com/karlesmarin/music-math}}
}
@misc{Marin2026PhaseTaxonomy,
  author = {Mar\'in, Carles},
  title  = {The Phase Taxonomy of Pitch-Class Set Invariants},
  year   = {2026}, doi = {10.5281/zenodo.20826773},
  note   = {Note 2, Mathematics of Music series. \url{https://github.com/karlesmarin/music-math}}
}
@misc{Marin2026TonnetzSpectrum,
  author = {Mar\'in, Carles},
  title  = {The Tonnetz Spectrum is the Generating Triad's Fourier Balance Profile},
  year   = {2026}, doi = {10.5281/zenodo.20862821},
  note   = {Note 3, Mathematics of Music series. \url{https://github.com/karlesmarin/music-math}}
}
```

Each note is archived on Zenodo with a concept DOI (all versions) and a version DOI:

| Note | Concept DOI (cite this) | This version |
|---|---|---|
| 1 — 6-30 self-duality | [10.5281/zenodo.20820961](https://doi.org/10.5281/zenodo.20820961) | [20820962](https://doi.org/10.5281/zenodo.20820962) |
| 2 — phase taxonomy | [10.5281/zenodo.20826773](https://doi.org/10.5281/zenodo.20826773) | [20826774](https://doi.org/10.5281/zenodo.20826774) |
| 3 — Tonnetz spectrum | [10.5281/zenodo.20862821](https://doi.org/10.5281/zenodo.20862821) | [20862822](https://doi.org/10.5281/zenodo.20862822) |

## ⚖️ Author and license

Carles Marín (independent researcher, karlesmarin@gmail.com). A large language model was used as a
coding assistant; every statement was independently verified by the Lean kernel, and all mathematics and
claims are the author's responsibility.

Licensed under the Apache License 2.0 — see [`LICENSE`](LICENSE).
