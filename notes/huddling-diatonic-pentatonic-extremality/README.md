# 🎼 Huddling, diatonic and pentatonic scales in Z12

**Fourier maxima and convex-energy minima formalized in Lean 4** — October 2026, version 1.1.

📄 [English PDF](huddling_note.pdf) · 📄 [PDF castellano](huddling_note_es.pdf) ·
📝 [English LaTeX](huddling_note.tex) · 📝 [LaTeX castellano](huddling_note_es.tex).

Note 5 of the Mathematics of Music series. Version 1.0 was published as
[10.5281/zenodo.23121104](https://doi.org/10.5281/zenodo.23121104).
Version 1.1 is [published at 10.5281/zenodo.23123219](https://doi.org/10.5281/zenodo.23123219).
The Spanish version uses Babel, including Spanish table captions; both versions share colored tables.

The note follows one question: why do the diatonic white keys maximize a Fourier magnitude
and minimize every strictly admissible all-pairs energy? Huddling and multiplication by five
identify the Fourier equality class; double Abel summation identifies the same energy class.
Complementation carries the result to the pentatonic black keys without another census.
The final sections connect this to homometry, parity, and the tritone in the earlier notes.

The mathematics is classical. The contribution is the connected formalization and explicit
trust audit. The [literature comparison](../../literature_novelty_2026-10-03.json) records positive
antecedents, including Amiot (2006/2007), Douthett–Krantz (2007), and Bushaw–Cody–Leffler
(2024, revised 2025). The [formalization audit](../../formalization_prior_art_2026-10-03.json)
found no matching implementation in its bounded search; it does not establish universal priority.

## 🧩 Formal statements

**Current-source update (3 October 2026):** the general cyclic Huddling theorem
and its equality case are now proved symbolically and used by the twelve-tone
library. Euler's formula gives the explicit sine-ratio constant, with
`sin(7π/12)/sin(π/12) = sin(5π/12)/sin(π/12) = 2 + sqrt(3)`.
See the [connection and trust update](../../research/EULER_TO_HUDDLING_2026-10-03.md).
The archived v1.1 PDFs describe the earlier implementation.

| File | Main role |
|---|---|
| [MTransform.lean](../../lean/MTransform.lean) | Fourier index permutation; exact comparison in Z[sqrt(3)]. |
| [Huddling.lean](../../lean/Huddling.lean) | All-cardinality maximum and equality class in ZMod 12. |
| [CyclicHuddlingGeometry.lean](../../lean/CyclicHuddlingGeometry.lean) | General nonzero cyclic order: sharp inequality and full equality classification. |
| [CyclicHuddlingClosedForm.lean](../../lean/CyclicHuddlingClosedForm.lean) | Euler's chord-length formula gives the sine-ratio bound and complement symmetry. |
| [DiatonicExtremality.lean](../../lean/DiatonicExtremality.lean) | Seven-note Fourier–energy equivalence for strict admissible potentials. |
| [ExtremalityConnections.lean](../../lean/ExtremalityConnections.lean) | Symbolic complement-energy identity, pentatonic transport, homometry, parity, tritone. |
| [TranslationInvariantEnergy.lean](../../lean/TranslationInvariantEnergy.lean) | Finite-group complement normal form, energy-gap transport, and the twelve-tone hexachord bridge. |

The development reuses `Fourier.lean` and the symbolic Abel engine in `AllPairsEvenness.lean`.
The current spectral proofs use only the ordinary foundational axioms. The finite
energy certificate still uses `native_decide`, and the Fourier–energy equivalences
inherit that one compiled-evaluation dependency. The historical name
`Huddling.huddling_census` is retained for compatibility, with a structural proof.
The symbolic complement-energy and homometry-to-energy bridges introduce no new census.
Strictness is required for the shared equality class; weak convexity/decrease gives only a minimum.

## 🔧 Reproduce

From the repository root, with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
python huddling_verify.py
sage -python sage/huddling_check.py
python figs/huddling_figs.py --output-dir notes/huddling-diatonic-pentatonic-extremality/figs
python figs/huddling_figs.py --language es --output-dir notes/huddling-diatonic-pentatonic-extremality/figs
```

The Python check uses exact integer pairs and the Sage check computes directly in the
cyclotomic field. Matplotlib is required only for the figure. Build the PDF from this folder:

```sh
pdflatex -interaction=nonstopmode -halt-on-error huddling_note.tex
pdflatex -interaction=nonstopmode -halt-on-error huddling_note.tex
pdflatex -interaction=nonstopmode -halt-on-error huddling_note_es.tex
pdflatex -interaction=nonstopmode -halt-on-error huddling_note_es.tex
```

On Windows, `scripts/check_lean.ps1 -DependencyRoot <existing-lake-packages-directory>`
recompiles all local modules against an existing dependency cache, with the same implicit-variable
options as the Lake configuration. It writes logs and a JSON axiom report under `.work/checked/`.
This cached-dependency check was used during development; a fresh Lake dependency installation
is a separate reproducibility route. Recorded reports are in [verification](../../verification/).

## 🔗 A further connection

The separate [ComplementEnergy.lean](../../lean/ComplementEnergy.lean) module proves the
classical general finite weighted-kernel mechanism behind complement transport without
enumeration. Its scope and prior-art check are recorded in
[the addendum](../../complement_energy_audit_2026-10-03.json). The paper now states the
finite-group normal form and its twelve-tone specialization. Its pentatonic proof uses
`ExtremalityConnections.energy_compl`; `TranslationInvariantEnergy.lean` proves that
the general mechanism agrees with it when the diagonal potential is zero.

## 📜 License

The paper, translation and figures in this directory are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), following Note 4.
The accompanying software remains under the repository's [Apache 2.0 license](../../LICENSE).
