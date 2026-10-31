# Individual pieces in the actual HIGHBIN presentation

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.

## Exact result

`ActualPresentationGauge.lean` works with the repository's current
`ActualHighPresentation K c`. For an arbitrary family of complex values

```lean
z : ∀ Z T : ℝ, (b : HighBlockIndex K c Z T) → HighLabel K c Z T b → ℂ
```

the constructor `withPrescribedPieces K c P z` keeps the fixed arithmetic
Euler provider, companions, all three heights, labels, amplitude sets, means,
row membership and block values. At a label containing at least two
actual rows, it changes two contributions while preserving their sum.
If the chosen distinct rows are `u` and `v`, the replacement is

\[
f'(u)=z,\qquad f'(v)=f(v)+f(u)-z,
\]

with every other contribution unchanged. This is performed inside every
original label, so even the separate signed sum of each label is preserved.
The two aggregate identities required by `ActualHighPresentation` follow
without any new analytic assumption.

The following original propositions are definitionally unchanged:

- `FullHighEulerControl`;
- `HighPureNormPoleExclusion`;
- `HighConductorDeficit`;
- `HighLabelUniformity`.

The entire function `wholeBinBoundary K c P` is also unchanged. Yet for
each label with at least two rows the new pieces satisfy

\[
\lVert z(Z,T,b,\ell)\rVert\leq
\sum_{u\in A_\ell}\lVert P'.\mathrm{shiftedPiece}(Z,T,b,\ell,u)\rVert.
\]

`exists_presentation_preserving_inputs_with_large_piece_norm` specializes
this to any prescribed real threshold at a fixed original label.
The finite algebra is independently isolated in `FinitePieceGauge.lean`.

This result concerns arbitrary inhabitants of the existing presentation
type. The named `actualHighPresentation` can still have the desired
estimate after its concrete construction has been supplied. The audit
identifies why its aggregate identities alone do not provide the missing
individual-piece identification.

## The named Euler provider is now fixed

The continuation has replaced the freely chosen Euler field of
`ActualHighPresentation` with a derived accessor for the constructed
`arithmeticHighEulerData`. Its `rows_in_bin` and
`shifted_identification` fields use that same provider. The other
presentation fields and their required identities are retained. This
implements the task's explicit requirement that the still-admitted
HB-PRESENT construction use the actual arithmetic Euler data.

The original named `highInitialEulerControl` and
`highExceptionalEulerControl` now have source proofs using the genuine
initial calibration and finite exceptional-table bound. Their two
original `sorry` bodies have been removed; native checking of this
integration is still pending. The source change adds no equality
hypothesis identifying an unspecified provider and no field containing
either Euler conclusion. The exceptional estimate for a named
presentation still uses its recorded positive buffer and bin range;
the inherited HB-PRESENT dependency must be reported by the final
transitive axiom audit.

This provider binding does not construct `Base.highExpansion` or the
remaining fields of `actualHighPresentation`. It also does not identify
the original label pieces with the computed regions, or close the
original label-uniformity, norm-form and boundary obligations. The
gauge construction does not update an Euler field, so its finite
rebalancing argument continues to apply to the fixed-provider type.

## The construction needed by HB-NORMFORM

`Base.highExpansion` presently supplies bare `HighExpansion` data.
Its separately stated support property gives an upper ideal-norm envelope.
For the concrete restricted-height construction, the same named expansion
must additionally use the following objects by construction:

1. The finite grid code `Fin slots → Fin (N + 1)` for each amplitude label.
2. `actualRegionAmplitude` and `actualRegionMean` for its amplitude vector
   and mean.
3. `actualRegionRows` for its genuine finite row set.
4. `actualRegionPiece` for each individual shifted contribution.
5. The chosen internal contour height and the larger zero-detection height.

`ActualNormFormRegionPacket` already constructs these finite pieces and
proves their total integral identity. `ActualNormFormRegionTarget` proves
the original norm-form conclusion once the named presentation is
identified with those pieces. These are construction equalities, not
replacements for the desired analytic inequality. A verified completion
has to instantiate them for the same named expansion used downstream.

## A computed packet with exact integration at every scale

`ActualNormFormComputedPacket.lean` implements the packet directly in the
original `ModerateBlock` type. Given the assigned finite row set `F`, it
defines `integrableRows` by filtering `F` with integrability of the literal
`actualRegionKernel` on the complete height box. It then fills the block
with the actual grid, means, region row sets and restricted integrals.
The witness subdivisions are explicit supplied data recipes; the
constructor supplies no default recipe or saturation assertion.

This gate resolves the all-scale integration issue. A totalized Bochner
integral need not be finitely additive across a partition of a
nonintegrable function. For each retained row, the actual integrability
predicate gives the precise hypothesis needed by the partition theorem.
`computedRegionBlock_value_eq_pieces` therefore proves the complete
finite-label integral identity at every scale in the numerical contour
range.

In the eventual range of the actual norm-form theorem,
`exists_computedRegionBlock_normForm` proves `integrableRows = F`.
It derives full-box integrability from the theorem's integrability on
each of the finitely many actual regions. Thus every assigned row is
retained there. The same theorem supplies the norm form with the original
quarter-lambda loss and the actual full-slot upper and lower witnesses.
The block mean equals `actualRegionMean` by definition.

The label count is exactly `(N + 1)^slots`, and
`computedRegionLabel_count_bound` gives its uniform bound with height
degree zero. All small parameters and the label grid precede the scales,
rows and supplied witness subdivisions.

## The canonical masked detector blocks

`ActualCanonicalHighBin.lean` connects this packet to the actual finite
detector partition. Its `canonicalRows` uses the same `assignedRows` and
the same height `2 * internalHeight` as the boundary construction. It
applies an explicit finite source mask to the real nonprincipal shell
before selecting a detector fiber. This keeps a final shell's global
upper cutoff literal.

The retained block indices are the nonempty `retainedChoices`. The module
derives their bin range, ideal-norm envelope, nonprincipal-row condition,
source-mask membership and the stronger `2 * internalHeight + 2` buffer.
The full-shell case is recovered when the mask contains that shell.

`exists_canonicalBlock_normForm` selects one height exponent, one finite
amplitude grid and uniform constants. It then proves, for every scale,
shell, source mask, retained detector choice and supplied witness recipe
in the displayed range:

- all assigned rows pass the integrability gate;
- the block value equals the actual final contour summed over those same
  assigned rows;
- each label has the actual slot witnesses and the original
  `3/16 + moderateExponent ... + lam/4` norm bound.

The constants precede the source mask, so the latter may depend on the
scale. Means and pieces are defined by the actual regions throughout;
the theorem takes no label-mean or individual-piece identity as an input.
Its recursive project import closure contains none of `Base`, `HighBin`
or `Theta`, allowing the shared constructor to precede those named data.

## The direct target endpoint and the remaining named interface

`ActualCanonicalTarget.lean` specializes the constructor using only
`BaseContext`, `TargetArithmeticData`, and the actual Euler construction.
It sets the buffer to `min lamA lamB / 100`, takes companions `{1}`, and
derives the common row boundary from `FamilyContext.boundary`. The
existing target providers discharge allowed generators, mixed-Gauss
calibration and outside-S unramifiedness. No caller supplies these
calibrations or an identification with an unknown Euler provider.

`targetCanonicalNormForm` proves existence of numerical parameters.
`targetCanonicalParameters` chooses this tuple once, and
`targetCanonicalParameters_spec` proves the conclusion for that exact
choice. The record contains only numbers, with no analytic estimate
field. `chosenTargetCanonicalBlock` uses these same parameters at every
scale. The target dyadic-boundary endpoint uses the same buffer,
companions and detector, and provides scale exponent 14 with height
degree zero for a source mask that may depend on scale and height.

These constructed endpoints do not by themselves replace the old named
`highExpansion` or `actualHighPresentation`. Two concrete interfaces
still require a coordinated implementation:

1. **The actual expansion data.** The named expansion must be defined from
   the same finite shell schedule, retained detector fibers, amplitude
   grid, actual slot values and supplied witness recipes. Merely assuming
   equality of the old opaque expansion with this construction would
   leave the construction obligation unsolved. In particular, a recipe
   must be obtained from the real witness selection and saturation
   construction, not from an empty default or an admitted provider.
2. **The row set used in both contour sums.** The old presentation's
   `shifted_identification` integrates over the entire buffered raw bin.
   A canonical detector fiber is a subset of this bin; different raw
   bins may overlap. It cannot be replaced by the entire raw bin using
   the proven subset relation. A corrected presentation must use an
   explicit `fixedRows` field for both the initial and final contour
   sums, with these rows defined by the actual detector partition.

The generic packet retains an integrability gate even at small scales.
Its norm theorem proves that every assigned row passes the gate in the
eventual range. The additional `ActualFinalContourIntegrability` and
`ActualCanonicalIdentities` modules address the stronger target-range
identity directly: the actual denominator reciprocal extends across a
norm pole, while the numerator contour stays strictly to the left of
the pole line. Compact-box continuity then proves integrability for
every positive scale and every canonical detector fiber. For `Z > 0`
and `T ≥ 1`, their gate equality identifies the computed block with the
raw assigned-row final integral and identifies the boundary piece with
the initial integral minus that block. Removing the gate here uses this
analytic integrability theorem; it is not a definitional equality.

The minimal remaining proof interface is consequently about literal
data and exact integration: construct the common named block and recipe
data; identify the retained rows, full-slot amplitudes and individual
restricted integrals; and use the same fixed row set on both contours.
The norm-form estimate, exceptional Euler estimate and boundary decay
must remain conclusions of the existing analytic theorems. They must
not be supplied as fields or renamed hypotheses to this interface.

## Full correction and the moment polynomial

The source identity
`actualFullCorrectionSlot_decomposition` retains four actual terms:

\[
S_i=-M_i+E_i^{\mathrm{reg}}+E_i^{(1)}+E_i^{(\geq2)}.
\]

Here `M_i` is `actualCompensationMainSlot`, and the three errors are the
literal `actualRegularErrorSlot`, `actualValuationOneSlot` and
`actualRepeatedSlot`. The region packet's slot value is
`P^(4/25) * S_i` at one shared height point, with `P = primeScale g Z`.

On the line `Re z = 17/50`, the corresponding main term has the expected
central prime normalization: `4/25 + 17/50 - 1 = -1/2`.
The ratio `Norm p / P` and the imaginary height belong to its smooth
profile. This accounts for the main term's connection with a centrally
normalized Hecke prime polynomial. The three displayed error terms are
still present in the full slot.

Thus a common expansion for HIGHBIN and the moment modules must retain
the error-class labels and the repeated-prime allocations, or establish
the required moment estimates for the complete slots. The current
main-term polynomial identities by themselves identify only `M_i`.
This distinction is relevant when filling the actual `slotValue` fields
and the shared witness recipe.

## Verification

These support modules add no admitted declaration. The coordinated
`HighBin.lean` integration fixes the Euler provider and supplies source
proofs for the two original Euler obligations, as described above;
native verification of those named endpoints is not yet claimed.
`Base.highExpansion` and the remaining HB-PRESENT construction are
still admitted, and the original label-uniformity, HB-NORMFORM and
HB-MOVE-BOUNDARY obligations are not closed by the new canonical
constructors. Native build records are maintained with the
continuation's verification artifacts. The finite module has an
independent Mathlib-only import closure; the actual gauge adapter
imports `HighBin.lean` and therefore shares its upstream dependency
boundary.

The finite gauge module passed an unchanged-source native build with
Lean 4.35.0-rc3 and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8` in 274.055 seconds. The three
printed main declarations use only `propext`, `Classical.choice` and
`Quot.sound`; hashes and the exact scope are recorded in
`verified_piece_gauge.json`. This independent finite result does not
certify the actual packet or canonical-block dependency chains.

The actual packet, canonical-block and target-family implementations
remain source proofs awaiting their complete native dependency checks.
Their eventual norm bounds also inherit the existing
`PrimeNormalizer.window_prime_lower` admission (PR-WINDOW-PIT), through
`normalizer_smallPower` and
`exists_actual_primeNormalizer_inverse_subpower`. This is a distinct
upstream dependency, not a new assumption introduced by the packet.
Those analytic endpoints must therefore record their actual transitive
axioms rather than be described as using only the three standard Lean
axioms. The finite-label identities and cardinality statements are
audited separately.
