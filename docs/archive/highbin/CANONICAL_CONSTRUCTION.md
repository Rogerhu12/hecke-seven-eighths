# HIGHBIN continuation: canonical arithmetic row fibers (historical snapshot)

> **Historical snapshot — PR #7 at `d88663c8`.**
> Status statements, unresolved obligations and native evidence below describe
> that checkpoint and its earlier recorded stages. See the
> [current integration report](INTEGRATION_20261101.md) for shared interfaces
> and verification gates, and the
> [PR #7 description](https://github.com/Rogerhu12/hecke-seven-eighths/pull/7)
> for the latest commit, native results and acceptance status.

This branch continues the HIGHBIN task from commit
`8e45885f856b8c8b56287eec188be654682256ec`. It isolates the continuation
from the concurrently active original PR branch. This document describes
the construction; the verification report records compiler results.

## Corrected construction

The raw buffered-bin inequalities do not specify a unique bin for a row.
An exact decomposition must fix a row assignment before introducing
amplitude labels. In particular, containment in a raw bin cannot be used
as an equality with the sum over that entire raw bin.

`BufferedDetectorGeometry` and `ActualBoundaryGeometry` construct a
finite detector from the original common zero boundary. With
`M = ceil(1/e)` there are at most `(M+1)^2` detector choices. For each row,
a deterministic choice supplies a center `a` in `[51/100,B]`, a selected
zero unless it is the floor bin, and the upper zero-free buffer. The
chosen fibers cover the source rows, are pairwise disjoint, and preserve
finite sums. No count or detector estimate is an input.

The detector scale is `2*H`, where `H = max T (Z^kappa)`. Its contour
height is exactly `H`; its upper detector is at least `2*H+2`. These
inequalities provide the common geometry required by the norm-form
and contour-move arguments.

`DyadicCount`, `DyadicShells`, and `DyadicRowPartition` provide the literal
finite shell schedule and unique upper-closed assignment. The finite
source set remains a mask, including in the last shell. The shell count
is bounded by `(2+((upper-lower)/log 2)/eta)*Z^eta` for every `eta>0`.

`ActualDetectorBoundary` defines initial-minus-final integrals using
the same finite masked detector fiber on both contours. Its uniform
tail theorem has the order

```
exists Z0 >= 1, forall N : Nat, exists C > 0,
  forall ray source Z T kappa d,
    Z >= Z0 -> T >= 1 -> 1/16 <= d -> d <= 1 ->
    norm (maskedShellBoundary ...) <= C * Z^13 * T^(-N).
```

The hypotheses are `0<e<=1/10000`, `51/100<=B<=1`, `1` belongs to the
finite companion packet, the original common packet zero boundary, and
the stated number-field, Haar-measure and probe data. The bound is
uniform in the source mask, ray filter, internal-height exponent, and
shell. There is no input boundary estimate or height/count bound.

`ActualDyadicRows` identifies membership in the original frequency-row
envelope with its literal norm cutoff by reconstructing the ideal/sector
index. Its moderate source is exactly the nonprincipal rows with
`Z^(1/16) < Nu <= Z^upper`. The masked shells coincide with the proved
dyadic fibers, including the last shell and exact endpoint cases.

`ActualDyadicBoundary` sums these actual shells. Its whole-boundary tail
is `C*Z^14*T^(-N)`, with the threshold chosen before `N`; it supplies
`PowerHeightTailBound` with height degree zero. The indexed finite-sum
identity also identifies this boundary with the sum over the original
moderate source. Each row keeps its own detector-dependent `w` line.

`ActualCanonicalFamily` gives one dependent finite type for the actual
shell and its nonempty detector fiber. Its cardinality, rather than a
separately postulated block count, has every positive subpower bound.
The sum over its actual rows preserves the original moderate source.

`ActualNormFormComputedPacket` and `ActualCanonicalHighBin` populate
the original `ModerateBlock` using literal restricted-height integrals
of the full corrected amplitude. The label means, row sets, individual
pieces and block value are definitions. An integrability filter makes
the exact finite-integral identity valid at every scale; the uniform
norm theorem proves that this filter retains every assigned source row
throughout the eventual norm-form range. `ActualFinalContourIntegrability`
and `ActualCanonicalIdentities` additionally prove the gate is the original
assigned fiber for every `Z>0` and `T>=1` in the target contour range.
The denominator reciprocal extends analytically across a possible norm
pole; the numerator contour avoids its pole. Compact-box integrability
then gives the exact raw final-contour identity before an asymptotic
norm bound is invoked. It is not an assumed integrability statement.

The norm theorem chooses `kappa,theta,N,C,Z0` before the scale, external
height, shell, finite source mask, retained detector choice and witness
recipes. It supplies the quarter-loss norm-form estimate, actual slot
bounds, and equality between the block and the final contour integral
over precisely that assigned fiber. It retains the original calibrated
probe/character hypotheses and the upstream prime-window input. Its
witness recipes are explicit data: this constructor does not manufacture
an empty witness cover or assert the missing moment calibration.

`ActualCanonicalData` supplies the primitive original `TargetContext` data:
`e=min(lamA,lamB)/100`, companion packet `{1}`, the original calibrated
probe, its Haar measures, arithmetic Euler provider, and common zero
boundary. `ActualCanonicalEuler` proves the full actual row Euler input
and the regular/exceptional estimates for this very Euler provider. The
exceptional branch has constant `9` and cutoff `2`; its nonexceptional
prime alternative and arithmetic phase calibration are proved.
`ActualCanonicalTarget` chooses one numerical parameter tuple from the
proved norm-form existence theorem. The estimates for that tuple are proved by the choice
specification; no estimate is a caller-supplied field.

`ActualTargetFamily` fixes
`zeta=min(1/96,min(lamA,lamB)/100)` and `upper=13/16+zeta`, and ties this
same source mask and parameter tuple to the actual retained family. Its
norm theorem has the exact `lamB/4` loss of HB-NORMFORM. Its boundary
theorem concerns the same source and internal-height exponent.

## Acyclic arithmetic interface

`BaseContext` contains the primitive context and data declarations moved
verbatim out of `Base`. `TargetArithmeticData` similarly contains the
arithmetic calibration declarations moved verbatim from `Theta`.
`ActualTargetEuler` separates the target-only calibration declarations
from generic arithmetic Euler providers. The generic construction has
no import path through `Base`, `HighBin`, or `Theta`. Exact declaration
move hashes and import-graph checks are in the accompanying JSON files.

## What must not be inferred

The previous `actualHighPresentation` is still an admitted named value.
Its Euler accessor is now fixed by definition to the actual arithmetic
provider, and its two named Euler estimates have source proofs pending
native recheck. The remaining presentation data is still opaque.
Its fields constrain sums but do not identify each shifted piece.
`FinitePieceGauge` proves that two pieces can be changed with cancelling
increments while preserving the displayed finite sum; one individual
norm can then be arbitrarily large. `ActualPresentationGauge` transports
this observation to the presentation interface. This is an interface
insufficiency result, not a counterexample to the opaque named value.

The new constructor uses actual assigned row fibers and computed
pieces. It does not imply that the old admitted presentation or the
old admitted expansion already equals this constructor. The remaining
expansion/witness identification and any upstream admissions must be
reported explicitly. Source inventories and static dependency checks
are not compiler verification. New native compilation is in progress;
only exact-source exit-zero records count as passed.

## Historical verification checkpoint

The native GitHub Actions core job at commit
`4f733f5f9a616332feffeed212aed57972daf012` passed all 66 core modules and
533 public declarations. The audit permits only `propext`,
`Classical.choice`, and `Quot.sound`. This includes the detector geometry,
finite-piece gauge, dyadic count, strict-endpoint assignment, and finite
row partition. The exact commit, job, artifact, and source hashes are in
`verified_core_canonical_ci.json`. The actual arithmetic/integral
adapters and later actual-only files are not covered by that checkpoint.
