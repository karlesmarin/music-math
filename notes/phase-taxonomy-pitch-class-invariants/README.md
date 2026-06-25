# 🎶 The phase taxonomy of pitch-class set invariants

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20826773-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20826773)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](../../LICENSE)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean_4-Mathlib-2C2C2C)](https://leanprover.github.io/)

> Carles Marín (with Claude, Anthropic, as AI assistant). Zenodo DOI: [10.5281/zenodo.20826773](https://doi.org/10.5281/zenodo.20826773).
> Note #2 in the *Mathematics of Music* series (companions: Note #1, the 6-30 tritone self-duality; Note #3, the Tonnetz spectrum).

A focused, machine-checked research note. Over $\mathbb{Z}_{12}$, represent a pitch-class set $A$ by its
$0/1$ indicator and take the discrete Fourier transform $\hat A = |\hat A|\,e^{i\varphi}$. We show — and
verify in Lean 4 — that every classical invariant sorts by **how much of the phase $\varphi$ it retains**, a
ladder of increasing resolving power:

1. **Phase-blind (the power spectrum $|\hat A|^2$).** The interval vector, Babbitt's hexachord theorem,
   homometry / the $Z$-relation, deep scales, the rhythmic-oddity property and common-tones-under-$T$ are
   *all* functions of $|\hat A|^2$ alone — equivalently the autocorrelation, equivalently (in
   crystallography) the **Patterson function**. Homometry $\iff$ equal $|\hat A|^2$.
2. **Partial phase (the inversion index, $\hat A^2$).** Common tones under inversion — the sum / index
   vector — is a function of $\hat A^2$, which keeps only half the phase and is, as a set-class invariant,
   weak.
3. **The twist: third order (the bispectrum $\hat A\cdot\hat A\cdot\overline{\hat A}$).** The triple
   correlation is *also* phase-blind, yet over $\mathbb{Z}_{12}$ it **resolves the $Z$-relation completely**
   — separating homometric chords needs not more phase but higher order.
4. **Complete (the full $\hat A$).** Magnitude *and* phase together determine the set exactly.

The crystallographic crossing is rigorous, not analogy: autocorrelation $=$ Patterson function,
$|\hat A|^2 =$ X-ray diffraction intensity, the $Z$-relation $=$ the phase problem.

## 📄 Files
- `phase_taxonomy_note.pdf` / `.tex` — the note (English).
- `phase_taxonomy_note_es.pdf` / `.tex` — Spanish version.

## 🔧 Reproducibility
- **Lean 4** (`../../lean/`): `Fourier.lean` carries the whole ladder — the phase-blind floor
  (`homometric_iff_powerSpec_eq`, `IVraw_eq_invDFT_power`, `hexachord_IVraw_eq_nat`), the partial-phase
  inversion index (`commonTonesInv_eq_sumcorr`, `sumcorr_eq_invDFT`), the third-order resolution
  (`carterPair_triple_distinct`), and the complete-invariant capstone (`Ahat_eq_iff`). Compile against
  Mathlib; every named theorem audits to `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
- **Audio** (`../../media/`): MIDI + WAV sonifications, including the homometric Carter / $Z$-pair
  (`inversion_4z15`, `inversion_4z29`, `z_pair`) that the bispectrum separates.

## 🎯 Scope
Formalization + organization, not new mathematics. The Fourier balances are Lewin–Quinn; homometry / the
$Z$-relation and the Patterson crossing are classical (Patterson 1944; the crystallographic phase problem);
the bispectrum's resolving power is known in signal processing. The contribution is the **unified taxonomy**
— sorting the classical invariants by retained phase into one ladder, with its boundaries (the phase-blind
collapse, the third-order resolution, the complete-invariant capstone) machine-checked in one Lean file
with a clean axiom audit. A first formalization, not new theorems.
