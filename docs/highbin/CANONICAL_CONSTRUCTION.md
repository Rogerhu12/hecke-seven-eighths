# HIGHBIN continuation: canonical arithmetic row fibers

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

`ActualNormFormComputedPacket` and `ActualCanonicalHighBin` populate
the original `ModerateBlock` using literal restricted-height integrals
of the full corrected amplitude. The label means, row sets, individual
pieces and block value are definitions. An integrability filter makes
the exact finite-integral identity valid at every scale; the uniform
norm theorem proves that this filter retains every assigned source row
throughout the eventual norm-form range. It is not an assumed
integrability statement.

The norm theorem chooses `kappa,theta,N,C,Z0` before the scale, external
height, shell, finite source mask, retained detector choice and witness
recipes. It supplies the quarter-loss norm-form estimate, actual slot
bounds, and equality between the block and the final contour integral
over precisely that assigned fiber. It retains the original calibrated
probe/character hypotheses and the upstream prime-window input. Its
witness recipes are explicit data: this constructor does not manufacture
an empty witness cover or assert the missing moment calibration.

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
