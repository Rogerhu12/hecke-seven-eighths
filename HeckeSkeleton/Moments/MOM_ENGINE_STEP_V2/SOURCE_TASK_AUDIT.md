# Source blueprint task audit

This is a working specification review, not a declaration that the task
statements have passed CI. Every source task remains a draft until its
full import closure elaborates and the final assembly consumes it.

## Proposed proof units

| ID | Theorem file | Contract and output | Dependencies | Paper §4.8 lines | Expected proof size |
|---|---|---|---|---|---|
| S1 | `TasksFirstTransform.lean` | `FirstTransformTask`: original whole-centered finite source, fixed first log chart, genuine first zero/tail separation | Original call, source budget, exact complete coefficient dictionary | 2800–2828 | 3,000–4,000 lines |
| S2 | `TasksFirstAllowance.lean` | `FirstAllowanceTask`: exact common/D/S/character/side carrier, positive original allowances, Cauchy identity and supported physical windows | S1 realization; fixed input demand | 2827–2850 | Target 3,000–4,000 lines; see budget review below |
| S3 | `TasksAmplification.lean` | `AmplificationTask`: one pool outside all first-source indices; literal main/1/6/7 terms; separate direct zero-slot constructor | S1/S2 realizations and physical windows; fixed input demand | 2852–2881 | 3,000–4,000 lines |
| S4 | `TasksSecondTransform.lean` | `SecondTransformTask`: complete nonprimitive second correlation, original row-ball/log kernel, actual zero/tail/nonzero terms | S1/S2/S3 realizations and pool windows | 2883–2894, 3004–3010 | 3,000–4,000 lines |
| S5 | `TasksNominalGeometry.lean` | `NominalGeometryTask`: both side geometries, original width drop, nonnegative slack, correlation and row/support windows | Same complete source trace | 2895–2906 | Target 2,000–3,000 lines; see budget review below |
| S6 | `TasksFiniteLeaves.lean` | `FiniteLeafTask`: original cover dictionary; both full occurrence allocations; every live active leaf once; unchanged exceptional predicate | Same trace and S5 geometry | 2908–2925 | Target 3,000–4,000 lines; see budget review below |
| N8a | `TasksSourceIndex.lean` | `SourceIndexTask`: explicit two-common/two-divisor scalar ledger, original physical fibres and single-pool arithmetic mass | Same trace, S5 geometry and S6 exact finite raw carrier | 2842–2850, 2852–2881, 2895–2906 | 3,000–4,000 lines |

The estimates cover only the future proof of each task and its genuinely
needed local helpers. They do not justify importing the previous large
A-line implementation.

## Budget review and explicit forecast change

The first version of this review gave S2/S5/S6 upper bounds of
4.5/4.5/4.5k, against the public 4/3/4k. That was a real **+2.5k**
forecast, not an independent estimate that could be omitted from the
aggregate budget. The targets in the table above rely on the following
specific reuse and scope boundaries. They remain forecasts, not measured
completed proof sizes; an implementation exceeding a target must report
that difference before adding further helpers.

| Task | Concrete reusable statements | Work still required within this task | Scope excluded because another existing task owns it |
|---|---|---|---|
| S2 | `firstLeftAllowance_pos`, `firstRightAllowance_pos`, `first_allowance_scalar_identity`; the already-proved first Cauchy reduction; `canonicalLogWithCoefficients_leftCoefficient_eq/rightCoefficient_eq`; `FirstFiniteSource.divisorPhysicalCutoff_le_supported` | One side-parametric original nonzero-rectangle norm window, uniform annulus-to-small-power threshold, physical divisor norm/radius transport, exact finite Bool/character summation. Planned allocation: 1.2k norm windows + 0.7k cutoff/rows + 0.5k threshold + 0.8k typed construction/Cauchy + 0.8k reserve = 4k. | First Poisson calibration is S1; first zero and tail estimates are T1/T4; global physical-index sums are N8a. No global union-column bound is needed here: the cutoff itself filters zero original pair profiles. |
| S5 | `NominalChildGeometry.width_identity`; `OriginalNominalGeometry.enlargement_bound`, `unit_length`, `radical_length`, `boundary_nonneg`; `FirstCommonCharacterBlock.secondCorrelation_norm_le`; `ActualSecondCorrelationRows.factor_eq_of_nonunitClassification` and `normFactor_eq_of_nonunitClassification` | Single actual row witness for each active class; same-pattern extraction transport; physical cutoff and support-product windows; side swap; logarithmic identities. Planned allocation: 0.6k geometry/transport + 0.4k direct base ledger applications + 1.0k physical row/support windows + 1.0k reserve = 3k. | No actual child parameters, clipping, capacity construction, or slot deletion is part of S5. Those belong to N3/N4/N6. |
| S6 | `ParentRawAtoms.originalAtlas/originalReindex`; `DirectGaussData.sourceCartesianCover`; `FirstGaussPoolData.mainSourceCartesianCover/residualSourceCartesianCover`; `ActualGaussStage.rawNonzeroCost_le_coverHybrid`; full-correlation finite leaf identity; `ActualHybridLeaf.costs_zero_of_not_live` and row-zero lemmas | One generic original cover transport used for direct/main/error labels, exact full-allocation finite enumeration, positive outer scalar transport, zero-correlation/zero-column removal. Planned allocation: 1.4k cover dictionary + 0.8k finite sums/Fubini + 0.7k active filtering + 0.5k indexing + 0.6k reserve = 4k. | No centered rectangle factorization or profile scalar dictionary is proved here (N1/N5a); no exceptional arithmetic recovery (T3a); no passive mask refinement (N2). |

In particular, the A-line-only theorems
`canonicalComparison_column_norm_le_fixed_power` and
`canonicalFirstDirectLogBlock_row_windows` are **not** being counted as
existing base inputs. Their narrow supported-window content must be
proved within the S2 allocation above. Likewise, no line saving relies
on importing an A-line implementation wrapper.

## Existing base boundaries

- **S1:** `CanonicalRowBallChart`, `ParentConstantSource`,
  `CanonicalFirstLogChart`, `ActualDirectFirstSource`, and the complete
  source budget. The original full support changes only the internal
  `m/q` split; the same total width and row polynomial must be preserved.
- **S2:** `FirstBlockDirectData`, `DirectFirstReduction`,
  `FirstDivisorPhysicalSource`, `FirstDivisorNormCalibration`.
  The base `FirstBlockDirectData` record already pins its columns,
  residual ideals and generators; its original coefficients are computed
  from the actual chart. The blueprint additionally pins rows and the
  exact row-weight supremum.
- **S3:** `FirstGaussPoolData`, `FirstDivisorPool`, `GaussPoolDictionary`,
  `ArithmeticPrimePool`. The pool is a field of `PoolPresentation`, before
  the first-source and valuation indices. No row-dependent fresh pool is
  allowed. The two local density exponents use the actual row norm and
  first residual divisor.
- **S4:** `ActualGaussRawTerminal`, `SecondCommonSource`,
  `CanonicalSecondLogChart`, `ActualFrequencyClassStability`. Genuine
  truncation discrepancies are kept as norms of the complete sums.
- **S5:** `ActualNominalGeometry`, actual unit/nonunit frequency radicals,
  and the complete-correlation bounds. The base physical cutoff uses
  only nonzero original pair profiles (`FirstFiniteSource.inverseRadii`),
  so supported column windows suffice without deleting original zero
  columns.
- **S6:** `SourceCartesianCover`, `SourceCartesianAtlas`,
  `CoverHybridPhaseIntegral`, `HybridFiniteLeaf`, `HybridLeafSupport`,
  and `HybridLeafRowZero`. The exact finite cover cannot duplicate an
  original extraction label.
- **N8a:** `FiniteBranchIndex`, `TwoDivisorLabelMass`,
  `AmplifiedFiniteIndex`, `FiniteBranchMass`, and original divisor/row
  fibre estimates. No normalized child or kernel appears in this task.

## A-line reference scope

Use the A-line first-source/full-support constructions for S1/S2;
primitive pool and direct preparations for S3/S4; pattern child windows
and nominal geometry for S5; actual covered leaf and exact original
atlas constructions for S6. For N8a the relevant references are
`CanonicalLiteralPrimitiveDirectGlobalMass`,
`CanonicalLiteralPrimitivePooledGlobalMass`, and their actual arithmetic
index/fibre helpers. These references explain the index maps and cost
bookkeeping; the large literal atom/profile/factory wrappers are not
part of the blueprint dependency closure.

## Mathematical checks and corrections

1. The original empty-row case is handled before S1 by the separate
   zero output. `FirstPresentation.Realizes.active` propagates the actual
   original row witness through the complete source trace.
2. `PairedEngineDomain` already supplies `3/4 ≤ κ ≤ 1`; no extra global
   hypothesis on the target context is introduced.
3. The two cutoff exponents are strictly positive. The loss is bounded
   both by the step and by the original reserve divided by the slot cap.
4. All original profiles, kernels, scalar weights, finite labels and
   column multipliers are fixed by exact identities. Later estimates do
   not quantify over arbitrary rescaled analytic data.
5. The full first deletion mask remains distinct from its actual paid
   moving support. Error valuation six can add a passive deletion prime
   without charging it as a new moving support factor.
6. The packet retains the original first reciprocity element, first
   Fourier side and removed pool prime power. These three fields are
   fixed by the original first key and pool tag, enabling an explicit
   original normalizer rather than an arbitrary quotient certificate.
7. Base `ActualHybridLeaf.Live` does not test its correlation row weight.
   The raw family therefore enumerates `Live ∧ class.Active`. S6 must
   show that omitted zero-correlation classes have both original costs
   zero. This is a proof obligation, not an extra source assumption.
8. Empty physical first rows already force the exact orbital fibre
   supremum, second-stage fibre and leaf weight to vanish. No extra
   modification of the canonical kernel or profile is necessary.
9. The local N8a ledger is
   `poolPrefactor * |μ S₁| * |μ L₂| /
   (Norm rad(C₁,D₁) * Norm rad(C₂,D₂) * Norm L₂)`.
   Main has its original pool-length allowance; errors have the original
   moving prime power. Its constant and scale threshold are chosen
   before the call and its physical indices.
10. N8b should pay only the later passive, allocation-normalization and
    active-capacity fibres, plus the original Fourier/profile factor.
    Combining that independent work with N8a is the concrete reason the
    previous single N8 unit risked exceeding 5,000 proof lines.

## Assembly status

`Blueprint.SourceCertificate` is the real certificate record.
`Assembly.sourceCertificate` has a complete proof from the six explicit
S1–S6 task premises. It imports no `Tasks*.lean` theorem and contains no
`sorry`; CI still has to elaborate the full source closure.
