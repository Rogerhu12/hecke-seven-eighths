# T3a / T3b shared proof sources

The following existing N1 implementation is reused verbatim from PR #32, commit `6caa522ba57bb248e62e4dd3499f7776ff20167d`. T3b uses the universal original-row atom formula, not the ordinary-only certificate. These modules retain their original names so B-line integration can share one implementation.

Root: `OrdinaryRawAtomFormula.lean`, specifically `RawLeafPacket.beforeAtomTable_left` and `beforeAtomTable_right`.

- `OrdinaryAtomExtraction.lean`
- `OrdinaryAtomModel.lean`
- `OrdinaryCharacterFacts.lean`
- `OrdinaryDivisorGate.lean`
- `OrdinaryFirstAtomFormula.lean`
- `OrdinaryLeafBinding.lean`
- `OrdinaryLeafLocations.lean`
- `OrdinaryMultiplierTransport.lean`
- `OrdinaryNormPower.lean`
- `OrdinaryNormProfile.lean`
- `OrdinaryOccurrenceFacts.lean`
- `OrdinaryOriginalCoordinates.lean`
- `OrdinaryOriginalTerms.lean`
- `OrdinaryPhaseCoefficients.lean`
- `OrdinaryPhaseFacts.lean`
- `OrdinaryPointTransport.lean`
- `OrdinaryRawAtomData.lean`
- `OrdinaryRawAtomFormula.lean`
- `OrdinaryRectangleFactors.lean`
- `OrdinaryScaleFacts.lean`
- `OrdinarySourceFacts.lean`
- `OrdinarySourceTransport.lean`

Original snapshot: 4431 physical lines. CI-driven compatibility changes are recorded below and reported in the PR #31 coordination thread.

### CI compatibility correction

Commit `3cfd114086b29724da88721d9f5f7dfeaa379bde` changes only the two proof steps in
`OrdinaryCharacterFacts.twist_plain` and `twist_prime`: the exact singleton identity
is transported with `congrArg` instead of `rw`, which was unable to match the
semireducible exterior-ideal projection in CI. Statements, characters, masks and
source coefficients are unchanged. The diagnostics are from run `41448321827`,
job `125286921697`; the shared-owner coordination is PR #31 comment `6578016005`.

## N4 frozen ideals and scale identities

Reused verbatim from PR #39 candidate `d98ab940632fbc73127ac655493f89b5af6f67ef`:

- `N4ScaleProduct.lean`
- `N4FrozenIdeals.lean`

This 473-line minimal closure proves the actual first frozen ideal includes the complete pool valuation, and the second frozen ideal is the actual common ideal. T3b uses the universal packet identities, without importing an ordinary-only certificate or any placeholder task.

## B-line CI repair

`OriginalPhaseData.lean` is synchronized verbatim with B-line
`ad4f0a10927063901caae60440f8c3847f232231` (local principal-ideal instance).
The shared process watchdog introduced at that commit remains in the newer
public driver recorded below.

`RawContracts.lean` and `OrdinaryData.lean` are synchronized verbatim with B-line
`1f5849c7025a1bd57589ab3d3e580503a159a3c3`: local structure-generation options,
synchronous elaboration and flushed command checkpoints, plus explicit existing
context parameters in `RawCovers.leaf`, the original arithmetic data in
`OrdinaryData.branch`, and the complete original telescope in `OrdinaryBinding`.
`SourceIndexContracts.lean` also follows that exact B snapshot: the two existing
Möbius factors are fully namespace-qualified. Mathematical fields, carrier
types, coefficients and task statements are preserved.

## N8 original frozen-profile and common-scalar bounds

Originally split in PR #42 candidate `773795d60dabbb136311e8187e21d130714e3aeb`,
following PR #31 comments `6578016005`, `6578119255` and `6578269366`.
The upstream snapshot is `8cda5bb1ad0785d9ee862e0ef868f802f252d8e8`, with the
additional CI compatibility correction recorded below:

- `N8FrozenProfileBounds.lean` (100 lines)
- `N8CommonScalarBounds.lean` (251 lines)

The update changes only the nonnegative finite-product API to `prod_le_prod₀`
and supplies the existing arithmetic data/embedding parameters explicitly in
the envelope bound. Statements and original scalar formulas are unchanged.

Run `41454774485`, job `125308565392`, also exposed the omission of the section
variable `input` from `commonAnnulus_nonneg` and `original_slot_window`.
Both intended input-dot helper methods now use `include input in`, preserving
the original inequalities and proof bodies while retaining the `ProfileInput`
argument needed by their existing callers and the latter proof's raw fields.
This exact two-line compatibility patch is coordinated with N8 in PR #31.

Run `41458052013`, job `125319706480`, then exposed an unmatched simplifier
rewrite in `original_slot_window`. The nonzero representative proof now applies
`input.raw.prime_eq i 0 _` in its original direction and composes it with the
assumed zero equality before invoking the original-profile nonzero hypothesis.
The profile, evaluation point and window statement are unchanged; the exact
patch is recorded in PR #31 comment `6579471045`.

These two modules preserve the upstream public names and original prime
profiles, complete common frozen ideals and pointwise scalar estimates.
The second exceptional common bound is constructed in `T3bCommonBounds`
on the actual universal `firstAtomTable`; it uses no ordinary-data
hypothesis. The two private upstream scale-positivity helpers no longer
conflict with the existing public N1 declarations. No N8 task proof or
ordinary normalized-mass certificate is imported.


## CI synchronization and shared dependency diagnostics

The public V2 driver `.github/v2/build.py` follows B commit
`1f5849c7025a1bd57589ab3d3e580503a159a3c3` verbatim, including its strict
300-second per-module watchdog and the typed `moduleNames` cache accepted in
PR #31 comment `6578888764`. The selected declaration set and axiom whitelist
are unchanged. Public manifest task scopes follow the same B commit, with
`t3_shared_n8` included in this branch's explicit
94-module T3 scope. The separate T3 proof job also requires both task endpoints.

The diagnostic script follows N7 commit
`054b434f2acab53a1ff5e7cfc79e56ea06803cbf`, including explicit `IO Unit` markers,
filtered console output and exclusion of toolchain imports from Lake targets.
The probe imports remain complete. Its safety assertion is synchronized to B's
new 300-second timeout and the value is recorded in diagnostic results.
This branch probes RawContracts; N7 probes OrdinaryData. Temporary instrumented
source output is diagnostic only and cannot replace the canonical build or axiom audit.
