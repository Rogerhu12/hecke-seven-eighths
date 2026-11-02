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
