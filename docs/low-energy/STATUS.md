# Low reflected energy: proof and integration status

This branch develops `HeckeSkeleton.completedMarkedEnergy` against the real
definitions in `Rogerhu12/hecke-seven-eighths`, starting at
`503ad9895e5f8affef55b22fea082e251bf33aa7` on `dtests-handoff`.

**Current review state: work in progress.** The existing `completedMarkedEnergy`
admission has not yet been replaced. The new source files contain no `sorry`,
`axiom`, `admit`, or `native_decide`. The per-file manifest distinguishes source
that has actually compiled from adapters awaiting verification. This document
does not claim that the final energy theorem or the complete repository builds.

## Mathematical route

The actual marked row is kept intact before the norm is taken. The hybrid
estimate retains the original squarefree row and both coprimality masks. Its
analytic inputs are exactly the arbitrary-coefficient quadratic and cubic
large sieves, together with the actual character identities. The coefficient
of the two dual columns is independent of the moving row and active marks.

The new core proves the four-scale hybrid estimate, the common-profile Mellin
integral estimate, the finite local Weyl table, the minimum/cube norm charges,
the full dual-tail exponent estimate, powerful-ideal Rankin bounds, and the
Gaussian annulus/dual-dyad summation. The physical polynomial keeps the
powerful ideal's inverse half norm; no second powerful-row count is introduced.

The actual adapters instantiate the original symbols and exterior ideals,
retain all sixth-unit sectors, reindex the original reflection coefficients,
carry the window and conjugate Hecke weights, and express the full row as
finite blocks and absolutely convergent dual dyads. The local fixed-block
estimate invokes the proved hybrid theorem rather than assuming an energy
bound. The remaining integration work is the final uniform assembly into the
exact target cutoff and selected-ideal denominator, followed by compilation.

## Verification

The pinned environment is Lean `4.35.0-rc3` and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`. The manifest records exact source
hashes and successful local checks; unverified files are explicitly labeled.
The standalone core currently has 50 matching successful module checks.
Printed public theorem audits for these checked modules contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Run `python3 scripts/low_energy_verify.py core` and
`python3 scripts/low_energy_verify.py actual` after obtaining the pinned Lake
dependencies and Mathlib cache. The verifier compiles actual repository sources
in dependency order, uses the repository's implicit-argument options, records
source hashes, and preserves compiler and axiom output. GitHub Actions runs
the two phases independently. A running job or an uploaded source file is not
counted as a successful verification.

Some vendored files originally imported the whole of Mathlib. This branch
replaces those broad imports with `FLTReuse.ExplicitMathlibImports`, a module
consisting only of explicit official Mathlib imports. Their definitions and
proofs are unchanged. The import-change manifest records their original and
modified hashes; the same sources are used locally and in CI.

## Scope and hypotheses

The intended final theorem takes `MarkedCoefficientReflectionInput`,
`QuadraticSieveBound`, and `CubicSieveBound` explicitly, as permitted by the
task. No completed-energy, separated-energy, row-majorant, or equivalent
analytic conclusion is accepted as an extra external hypothesis.

`source_manifest.json` gives the exact source files and their current check
state. Public main theorem statements and all hypotheses remain in those
Lean files; the final integration statement will be recorded here when it
has been completed and verified.

AI-assisted development; proof claims are limited to the recorded Lean checks.
