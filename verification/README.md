# 🧪 Verification record — 2026-10-03

`library_compile_manifest.json` records the source hashes of all 21 substantive Lean modules,
each compiled successfully against the pinned dependency cache. `extremality_build_report.json`
contains a subsequent successful run of the six-module dependency closure of the new note,
including its per-theorem axiom reports. The manifest explains the initial reporting-only failure.
Individual compiler logs are included here.

`complement_build_report.json` records the separate successful compilation of the general
finite weighted-kernel module `ComplementEnergy.lean`. Its five audited statements use only
`propext`, `Classical.choice`, and `Quot.sound`, without native evaluation or enumeration.

The later connected continuation is summarized in [CONNECTIONS_2026-10-03.md](CONNECTIONS_2026-10-03.md).
Its new translation-invariant and homometry/complement declarations were compiled directly with
the same pinned Lean and Mathlib cache; their axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The diatonic and pentatonic Fourier–energy equivalences each use the ordinary foundational axioms
and two native census dependencies. `ExtremalityConnections.energy_compl` and
`energy_eq_of_homometric` use only `propext`, `Classical.choice`, and `Quot.sound`.
No axiom report contains `sorryAx`.

These are direct Lean compiler checks using cached dependencies, with the implicit-variable options
from `lakefile.lean`. The Lake configuration itself was typechecked. A fresh download followed by
`lake build` was not performed in this session.

Independent arithmetic validation is reproduced with `python huddling_verify.py` and
`sage -python sage/huddling_check.py` from the repository root. The paper documents the exact
scope: 4096 subsets for Huddling, 792 seven-note subsets for the diatonic extremality comparison.
