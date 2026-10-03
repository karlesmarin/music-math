# Euler → roots of unity → Huddling → diatonic and pentatonic constants

The [Theorem of the Day sheet supplied by the author](https://www.theoremoftheday.org/GeometryAndTrigonometry/EulerIdentity/TotDEulerIdentity.pdf)
uses `τ = 2π` and states `exp(iτ/2) = -1`. It recalls Euler's circle formula
from the 1748 *Introductio*. That identity is already formalized in Mathlib;
we reuse the existing results. The new work here is their integration into
the music-math proof chain, with no claim of new mathematics or priority.

## Existing Mathlib results

| Declaration | Role |
|---|---|
| [`Complex.exp_mul_I`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Trigonometric.html#Complex.exp_mul_I) | Euler's exponential/cosine/sine formula. |
| [`Complex.exp_pi_mul_I`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.html#Complex.exp_pi_mul_I) | The identity `exp(πi) = -1`. |
| [`Complex.exp_two_pi_mul_I`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.html#Complex.exp_two_pi_mul_I) | A full turn exponentiates to one. |
| [`Complex.norm_exp_I_mul_ofReal_sub_one`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Trigonometric.html#Complex.norm_exp_I_mul_ofReal_sub_one) | The chord length `|exp(ix)-1| = 2|sin(x/2)|`. |

The pinned local Mathlib source contains all four declarations. The relevant
revision is `701fb6e9c3b9285968b375d19886bfc5ca134840`.

## What this connects

Put `ζ = exp(-2πi/N)` and let `C_m = {0,...,m-1}`. The already formalized
geometric-series identity gives

\[
  \widehat C_m(1)(\zeta-1)=\zeta^m-1.
\]

Taking norms and applying the chord-length identity turns the sharp arc bound
into an explicit real formula. For `N > 1`, `0 ≤ m ≤ N`, and a unit frequency `k`,

\[
  |\widehat A(k)|\leq \frac{\sin(\pi m/N)}{\sin(\pi/N)},\qquad |A|=m.
\]

Equality holds exactly when multiplication by `k` sends `A` to a translated
consecutive arc. This is `norm_Ahat_unit_eq_sine_ratio_iff` in
`lean/CyclicHuddlingClosedForm.lean`. The denominator is proved positive;
`N = 1` is covered by the geometric theorem rather than this quotient.

Sine complementation, `sin(π-x)=sin(x)`, gives the same bound for `m` and `N-m`.
It is the explicit-constant counterpart of the Fourier complement identity.
In twelve tones, the current library also verifies

\[
 \frac{\sin(7\pi/12)}{\sin(\pi/12)}
 =\frac{\sin(5\pi/12)}{\sin(\pi/12)}=2+\sqrt3.
\]

The declarations are `DiatonicExtremality.diatonic_sine_ratio_value` and
`DiatonicExtremality.pentatonic_sine_ratio_value`.

## Trust change in the current sources

`Huddling.arc_maximizes_power` and `arc_unique` now specialize the general
symbolic proof. The historically named `huddling_census` remains available for
compatibility, but its proof also derives from that structural theorem.
No subset census or `native_decide` is used by the current Huddling theorem.

The diatonic Fourier maximum, its equality characterization, and the radical
and sine-ratio constants consequently have only the ordinary foundational
axioms. The convex-energy side still uses `DiatonicExtremality.energy_census`;
the Fourier/energy equivalences inherit that one native dependency. Their
remaining census has not been replaced by the spectral proof.

The published Note 5 v1.1 PDFs describe the earlier two-census implementation.
They remain that version's archival documents; the current-source changes and
the proof audit are documented separately here. The compilation evidence is
`verification/euler_huddling_build_report.json`.
