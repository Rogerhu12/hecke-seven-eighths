# Constructed buffered detector and boundary

The detector is now a finite construction on the repository's literal
`rowZeroAbove` and `rowZeroBelow` predicates. Its input is the original
common packet boundary. It does not take a contour estimate, a block-count
estimate, an amplitude estimate, or a preselected geometry as a hypothesis.

## The finite choice

For `e > 0`, set

\[
M=\lceil 1/e\rceil,\qquad a_j=51/100+je.
\]

At height `3(i+1)L`, let `j_i` be the largest index `j ≤ M` for which
the actual row has a zero above `a_j`; retain `j=0` as the floor convention
even when there is no such zero. The values `j_i` belong to `0,...,M`.
There is an `i ≤ M` with `j_(i+1) ≤ j_i`, since otherwise the first
`M+1` strict increases would leave that range. Maximality then excludes a
zero above `a_(j_i+1)` at height `3(i+2)L`. This proves the buffered upper
condition at `a_(j_i)+2e`. When `j_i > 0`, the selected zero is part of
the original `rowZeroAbove` proposition. The common packet boundary gives
`a_(j_i) ≤ B`; the floor uses `51/100 ≤ B`.

The construction does not require a finite zero-count theorem. Only a
finite grid of threshold predicates is examined. A classical finite
choice selects one admissible pair for each actual frequency row.

The source modules are:

- `HeckeSkeleton/HighBinSupport/BufferedDetectorGeometry.lean`:
  finite pigeonhole argument, grid, heights and index count;
- `HeckeSkeleton/HighBinSupport/ActualBoundaryGeometry.lean`:
  actual zero predicates, common-packet specialization, canonical row
  choice, disjoint fibers, exact finite-sum partition, raw-bin containment;
- `HeckeSkeleton/HighBinSupport/ActualDetectorBoundary.lean`:
  actual nonprincipal shells and the boundary estimate for the constructed
  finite family.

## The shared contour geometry

Set `H = max T (Z^kappa)` and run the detector at `L = 2H`. Its data are

\[
H_{\rm contour}=L/2=H,\qquad
H_{\rm selected}=3(i+1)L,\qquad
H_{\rm upper}=3(i+2)L.
\]

For `T ≥ 1`, this gives both `H ≥ T` and `H_upper ≥ 2H+2`.
Consequently the same choices satisfy the boundary's `H+3/2` buffer and
the norm-form estimate's stronger `2H+2` buffer. There are at most
`(ceil(1/e)+1)^2` nonempty choices per shell. For a finite list of `n`
shells, the ambient index type has cardinality
`n * (ceil(1/e)+1)^2`.

For `Theta = {1}`, its required companion membership is immediate.
`physicalRowFamily_zeroBelow_of_common_bound` derives the common detector
bound from the original `c.family.boundary`, because the representative is
in that packet and the row characters and trivial companion have finite
order. More generally, adjoining `1` preserves any given finite-order
companion set and its packet membership.

## The actual boundary statement

`exists_maskedShellBoundary_external_tail` has the following quantifier order.
Fix the number field, finite excluded set, actual probe and measures,
target character, finite companions containing `1`, window geometry,
`51/100 ≤ B ≤ 1`, and `0 < e ≤ 1/10000`. Assume the original common
boundary for the corresponding physical row families. Then

\[
\exists Z_0\ge1\;\forall N\in\mathbb N\;\exists C_N>0
\]

such that for every ray filter, every finite source row set `R`,
`Z ≥ Z0`, `T ≥ 1`, real `kappa`, and `1/16 ≤ d ≤ 1`, the boundary of the
constructed nonprincipal shell `Z^d < Nu ≤ 2 Z^d`, intersected with `R`, satisfies

\[
\lVert E_{\rm shell}(Z,T)\rVert\le C_N Z^{13}T^{-N}.
\]

Each summand is the original `rowContourBox` at `s=B+20e` minus the same
row set at `s=a+16e`, with `w=1-a-6e`, `z=17/50`, and contour height `H`.
The actual arithmetic Euler provider is used in both contours.

The source mask is literal intersection, implemented by
`maskedShellRows K S R Z d`. It preserves the global moderate cutoff in
the last dyadic shell. The estimate is uniform in `R`, and no source
cardinality estimate is assumed. `exists_shellBoundary_external_tail`
is the unmasked specialization obtained by taking `R` to be the full
original shell.

The proof requests internal decay order `N+6*#InfinitePlace(K)`, shortens
the available upper detector to `H+3/2`, and applies the existing proved
height-absorption inequality. Thus the height degree is zero and the
scale exponent is 13. Summing the explicit finite detector partition
only multiplies the constant by `(ceil(1/e)+1)^2`.

## Exact interface requirement

The canonical row fibers are subsets of the enclosing raw buffered
bins. They partition the source rows without duplication. The raw bins
themselves are not asserted to form a disjoint partition: a row may
satisfy the same buffered inequalities at several detector indices.

Therefore a presentation constructed from these data must retain its
selected `fixedRows` (or an equivalent fixed selector mask) in both its
initial and final contour sums. Replacing each fiber by its whole raw
enclosing bin is not justified by a support inclusion. This is a
specific requirement on the joint expansion/presentation constructor;
the new construction does not identify an arbitrary pre-existing
presentation with the canonical one.

Native arithmetic verification of the new modules is pending the
project dependency build. Source-level statements and candidate proof
terms are not by themselves a completed native verification claim.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
