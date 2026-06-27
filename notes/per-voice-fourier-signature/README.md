# 🎼 The per-voice Fourier signature: the bass is the spectrally purest voice

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20971089-1B6F8C?logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20971089)
[![License](https://img.shields.io/badge/License-Apache_2.0-B5530F)](../../LICENSE)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean_4-Mathlib-2C2C2C)](https://leanprover.github.io/)

> Carles Marín Muñoz (with Claude, Anthropic, as AI assistant). Zenodo DOI: [10.5281/zenodo.20971089](https://doi.org/10.5281/zenodo.20971089).
> Note #4 in the *Mathematics of Music* series (companions: Note #1, the 6-30 tritone self-duality; Note #2, the phase taxonomy; Note #3, the Tonnetz spectrum).

A focused empirical research note with a machine-checked kernel. For three centuries the bass has been
called the foundation — Rameau's *basse fondamentale*, the figured-bass tradition, Riemann's harmonic
functions — but always as a *structural* claim. The discrete-Fourier-transform-of-pitch-classes program
(Lewin–Quinn–Amiot–Yust) turns chord "qualities" into numbers (the magnitude $|a_k|$ of the $k$-th
coefficient: $|a_5|$ diatonicity, $|a_1|$ chromaticity, $|a_6|$ whole-toneness) but reads a piece by
**time**. This note turns it on the **voices**, and finds a measurable spectral fingerprint of the
foundation:

1. **The law.** Across **334 four-part Bach chorales** (and Palestrina), the **bass is the spectrally
   purest voice** — the lowest chromaticity $\alpha_1=|a_1|/|a_0|$ (paired $t=-20$) and whole-toneness
   $\alpha_6$ ($t=-15$) — *despite* using the widest pitch-class vocabulary (so not a cardinality artifact).
   The naive guess (that the fifth-walking bass is the most *diatonic*, $|a_5|$, voice) is **false**: that
   is the soprano. The inner voices, the alto above all, carry the most chromatic colour.
2. **The why: root realization, in two channels.** The bass is, to 95 % cosine fidelity, the chord-root
   distribution. Functional roots move by fifths/fourths (intervals 7 and 5, both **odd**): (i) odd steps
   flip pitch-class parity, balancing the two whole-tone collections, so $a_6\to 0$ (the *parity* channel);
   (ii) the bass's wide tessitura spreads its weight around the chromatic circle, so $a_1$ is low (the
   *dispersion* channel). It is **not** melodic semitone-avoidance (that correlation is $+0.01$).
3. **Texture-bounded.** The signature is strong in functional-bass homophony (Bach chorales, Palestrina)
   and fades in imitative (Monteverdi madrigals) and pre-functional (Trecento) textures — a **diagnostic of
   functional-bass writing**, whose boundary confirms the root-realization mechanism.

## 📄 Files
- `per_voice_note.pdf` / `.tex` — the note (English).
- `per_voice_note_es.pdf` / `.tex` — Spanish version.
- `figs/` — the five figures (per-voice camembert, Fourier profile, pitch-class clock, phase plane, historical sweep).

## 🔧 Reproducibility
- **Lean 4** (`../../lean/`): `ParityA6.lean` (built on `Fourier.lean`) — the certified kernel of the $a_6$
  channel: $\hat A(6)=\sum_{x\in A}(-1)^x=\#(\text{even pcs})-\#(\text{odd pcs})$, with $\hat A(6)=0\iff$
  parity balance, and the general even universe $\mathbb{Z}_{2m}$. Every named theorem audits to
  `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
- **Corpus** ([`music21`](https://web.mit.edu/music21/)): the per-voice characters are recomputed from the
  Bach chorales, Palestrina, Monteverdi and Trecento corpora; `../../viz/voice_figs.py` regenerates every
  figure from scratch (Python + matplotlib).
- **Audio** (`../../media/`): the four solo chorale voices (`bwv66_6_bass`/`tenor`/`alto`/`soprano`, MIDI +
  WAV) and the character archetypes that voice the $a_1$/$a_6$ channels (`arch_fifthchain`, `arch_chromatic`,
  `arch_wholetone`); the note's `[♭ audio]` links point here.

## 🎯 Scope
Empirical corpus law **+** a first formalization of its kernel — not new mathematics. The explanatory
ingredients are classical: the functional bass (Rameau, Riemann); the identity $a_6=$ pitch-class parity
(Amiot, *The Torii of Phases*); the single-note-move mechanism (Hoffman, *JMT* 52.2, 2008). The
`ParityA6.lean` kernel is the first machine-checked statement of that parity identity, and is *distinct*
from — not a corollary of — the tritone lemma (which concerns the *odd*-index coefficients). The per-voice
**magnitude** law itself is empirical (its mathematical kernel is the linearity of the DFT over the voice
decomposition), and is texture-bounded as above. We cite Yust (2017, 2019) and Amiot for the
DFT-of-distributions program, which reads textures by time; the per-voice (registral) magnitude contrast is
the orthogonal cut.
