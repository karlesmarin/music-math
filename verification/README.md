# 🧪 Verification record — 2026-10-03

`library_compile_manifest.json` records the source hashes of the 21 substantive Lean modules
in the initial audit, each compiled successfully against the pinned dependency cache.
Later additions have separate reports below; the initial manifest is not the current module inventory.
The historical `extremality_build_report.json`
contains a successful run of the original six-module dependency closure of the new note,
including its per-theorem axiom reports. The manifest explains the initial reporting-only failure.
Individual compiler logs are included here.

`complement_build_report.json` records the separate successful compilation of the general
finite weighted-kernel module `ComplementEnergy.lean`. Its five audited statements use only
`propext`, `Classical.choice`, and `Quot.sound`, without native evaluation or enumeration.

The later connected continuation is summarized in [CONNECTIONS_2026-10-03.md](CONNECTIONS_2026-10-03.md).
Its new translation-invariant and homometry/complement declarations were compiled directly with
the same pinned Lean and Mathlib cache; their axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

`cyclic_huddling_build_report.json` records the compiled general Huddling modules
`CyclicHuddling.lean` and `CyclicHuddlingGeometry.lean`, including source hashes and
axiom reports. Every listed result uses only the three ordinary foundational axioms.
The final declarations `norm_Ahat_one_le_arc`, `norm_Ahat_unit_le_arc`,
`norm_Ahat_one_eq_arc_iff`, `norm_Ahat_unit_eq_arc_iff`, and `maximizer_unit_iff`
are unconditional apart from the explicit nonzero-order and unit-frequency
assumptions. The geometric selector is proved, not left as a hypothesis.

`euler_huddling_build_report.json` supersedes the old extremality report for the
current source files. It recompiles the full dependency closure through
`ExtremalityConnections`, including the new sine-ratio module and the structural
replacement of the twelve-tone Huddling certificate. Its source hashes and logs
record the exact checked sources.
`source_sha256` hashes the actual compiler input. `source_lf_sha256` hashes the
same bytes after replacing CRLF with LF, matching Git's text normalization.
This records Windows/Linux line-ending differences explicitly rather than
treating them as changes to the Lean proof.

The current Huddling and diatonic spectral results use only ordinary foundational
axioms. The diatonic and pentatonic Fourier–energy equivalences each retain one
native dependency, from `DiatonicExtremality.energy_census`. The published v1.1
paper and its historical report describe the previous two-census implementation.
`ExtremalityConnections.energy_compl` and
`energy_eq_of_homometric` use only `propext`, `Classical.choice`, and `Quot.sound`.
No axiom report contains `sorryAx`.

These are direct Lean compiler checks using cached dependencies, with the implicit-variable options
from `lakefile.lean`. The Lake configuration itself was typechecked. A fresh download followed by
`lake build` was not performed in this session.

Independent arithmetic validation is reproduced with `python huddling_verify.py` and
`sage -python sage/huddling_check.py` from the repository root. The paper documents the exact
scope: 4096 subsets for Huddling, 792 seven-note subsets for the diatonic extremality comparison.
