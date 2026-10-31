# Individual pieces in the actual HIGHBIN presentation

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.

## Exact result

`ActualPresentationGauge.lean` works with the repository's original
`ActualHighPresentation K c`. For an arbitrary family of complex values

```lean
z : ∀ Z T : ℝ, (b : HighBlockIndex K c Z T) → HighLabel K c Z T b → ℂ
```

the constructor `withPrescribedPieces K c P z` keeps the original Euler
provider, companions, all three heights, labels, amplitude sets, means,
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

The source modules add no admitted declaration and do not alter
`Base.highExpansion`, `actualHighPresentation`, or the four original
HIGHBIN obligations. Native build records are maintained with the
continuation's verification artifacts. The finite module has an
independent Mathlib-only import closure; the actual adapter imports the
original `HighBin.lean` and therefore shares that module's upstream
dependency boundary.

The finite gauge module passed an unchanged-source native build with
Lean 4.35.0-rc3 and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8` in 274.055 seconds. The three
printed main declarations use only `propext`, `Classical.choice` and
`Quot.sound`; hashes and the exact scope are recorded in
`verified_piece_gauge.json`. This independent finite result does not
certify the actual packet or canonical-block dependency chains.
