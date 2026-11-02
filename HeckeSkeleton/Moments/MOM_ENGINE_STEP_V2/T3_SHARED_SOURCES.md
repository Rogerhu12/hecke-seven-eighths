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

Original snapshot: 4431 physical lines. Any CI-driven compatibility changes will be recorded in this task PR and sent to PR #32.

## N4 frozen ideals and scale identities

Reused verbatim from PR #39 candidate `d98ab940632fbc73127ac655493f89b5af6f67ef`:

- `N4ScaleProduct.lean`
- `N4FrozenIdeals.lean`

This 473-line minimal closure proves the actual first frozen ideal includes the complete pool valuation, and the second frozen ideal is the actual common ideal. T3b uses the universal packet identities, without importing an ordinary-only certificate or any placeholder task.

## B-line CI repair

`OriginalPhaseData.lean` and `.github/v2/build.py` are synchronized verbatim with B-line `ad4f0a10927063901caae60440f8c3847f232231` (local principal-ideal instance and the shared process watchdog).
