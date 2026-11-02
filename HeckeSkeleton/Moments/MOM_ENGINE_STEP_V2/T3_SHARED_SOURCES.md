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

`OriginalPhaseData.lean` and `.github/v2/build.py` are synchronized verbatim with B-line `ad4f0a10927063901caae60440f8c3847f232231` (local principal-ideal instance and the shared process watchdog).

`RawContracts.lean` and `OrdinaryData.lean` are synchronized verbatim with B-line
`9f44dd0c6f3acd958e851aa1a124f556ad24f6f8`: local structure-generation options only,
with all mathematical fields and task statements preserved.

## N8 original frozen-profile and common-scalar bounds

Reused verbatim from PR #42 candidate `773795d60dabbb136311e8187e21d130714e3aeb`,
following PR #31 comments `6578016005`, `6578119255` and `6578269366`:

- `N8FrozenProfileBounds.lean` (100 lines)
- `N8CommonScalarBounds.lean` (247 lines)

These two modules preserve the upstream public names and original prime
profiles, complete common frozen ideals and pointwise scalar estimates.
The second exceptional common bound is constructed in `T3bCommonBounds`
on the actual universal `firstAtomTable`; it uses no ordinary-data
hypothesis. The two private upstream scale-positivity helpers no longer
conflict with the existing public N1 declarations. No N8 task proof or
ordinary normalized-mass certificate is imported.
