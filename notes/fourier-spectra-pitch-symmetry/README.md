# 🎼 From the chromatic circle to the Tonnetz: the discrete Fourier transform as the eigenbasis of pitch-class symmetry

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20862821-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20862821)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](../../LICENSE)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean_4-Mathlib-2C2C2C)](https://leanprover.github.io/)

> Carles Marín (with Claude, Anthropic, as AI assistant). Zenodo DOI: [10.5281/zenodo.20862821](https://doi.org/10.5281/zenodo.20862821).
> Note #3 in the *Mathematics of Music* series (companions: Note #1, the 6-30 tritone self-duality; Note #2, the phase taxonomy).

A focused, machine-checked research note. The twelve pitch classes $\mathbb{Z}_{12}$ carry both the discrete
Fourier transform (the Lewin–Quinn *Fourier balances* $a_k$) and the geometry of the chromatic cycle graph
$C_{12}$. We show — and verify in Lean 4 — that the two share **one eigenbasis**, and follow that basis up the
ladder of pitch-class symmetry:

1. **Translation (abelian).** Every circulant / abelian Cayley graph is **diagonalized** by the DFT
   characters, with eigenvalue the connection set's Fourier coefficient (Babai's character sum; $2\cos(2\pi
   k/12)$ for $C_{12}$).
2. **Inversion (dihedral).** The $T/I$ group $D_{2N}$ is **block-diagonal** in the DFT basis, inversion
   pairing $a_k \leftrightarrow a_{-k}$ into **conjugate-pair** blocks, irreducible for $k\neq-k$; the DC term
   and the tritone are the two 1-dimensional blocks. The interval vector (Note #2's homometry invariant) is
   the power spectrum folded over these same pairs — one conjugate-pair object behind both notes.
3. **The Tonnetz (non-abelian).** The neo-Riemannian $PLR$-group's Cayley graph has spectrum
   $\pm\{3,\sqrt5,\sqrt3,1,2\cos(\pi/12),2\cos(5\pi/12)\}$, every value machine-checked by explicit
   eigenvectors — and **equal to the generating triad's own multiset of Fourier balances** ($\sqrt5=|a_3|$
   augmented, $\sqrt3=|a_4|$ diminished, $\ldots$).

## 📄 Files
- `spectral_note.pdf` / `.tex` — the note (English).
- `spectral_note_es.pdf` / `.tex` — Spanish version.

## 🔧 Reproducibility
- **Lean 4** (`../../lean/`): `CycleGraphSpectrum.lean` (R.1 + the abelian-Cayley spectrum C-2),
  `InversionDFT.lean` (the dihedral block decomposition, all $N$, + the conjugate-pair object),
  `TonnetzSpectrum.lean` (the full Tonnetz spectrum by explicit eigenvectors), `Fourier.lean` (the Note #2
  weld: `powerSpec_neg`, `IVraw_eq_powerSpec_conjPair`). Compile against Mathlib in the fast godsil
  environment; every named theorem audits to `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
- **Sage** (`../../sage/`): `tonnetz_cayley_spectrum.py` — the full Tonnetz adjacency spectrum, exact (integer
  characteristic polynomial; each $\rho_j(P+L+R)$ eigenvalue $= \pm|1+\omega^j+\omega^{9j}|$).
- **Figures** (`../../viz/`): `phase_gear_train.py` (transposition as a gear train), `torus_two_level.py`
  (the CRT torus $\mathbb{Z}_3\times\mathbb{Z}_4$), `solenoid_dyadic.py` (the dyadic 2-adic solenoid). Each
  re-runnable (Python + matplotlib).

## 🎯 Scope
Formalization + organization, not new mathematics. Circulant/Cayley spectra are folklore (Godsil–Royle;
Babai 1979); the dihedral irreducibles are standard representation theory; the Tonnetz Laplacian was
diagonalized by Lostanlen (2018). The contribution is the **unified, machine-checked** account — the first
formalization in any proof assistant of the circulant/abelian-Cayley spectrum and of the Fourier-basis
dihedral block decomposition — plus the expository observation that the Tonnetz adjacency spectrum is the
triad's own Fourier-balance profile (its components classical: Quinn/Amiot balances, Babai's Cayley sum,
Lostanlen's prior Laplacian diagonalization). We cite Prismriver (Aniva–Wang) for the prior Lean $T/I$
action, which our representation-theoretic and spectral layer extends. Spectral *completeness* (that the
certified eigenvalues are all of them) is Sage-witnessed, pending a Mathlib dihedral-irrep classification.
