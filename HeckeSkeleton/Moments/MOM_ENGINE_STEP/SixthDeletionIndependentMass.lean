import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionSeparateMass

set_option linter.unusedSectionVars false

/-!
# Full-deletion mass for two independent occurrence allocations

Passive deletion selects its left and right divisor allocations
independently. Their original arithmetic costs contain two separate
square-root divisor norms. The exact cost identity below retains both
of them; no equality between the two divisors is an input.

The same chosen normalized children are used throughout. Their
sixth-root bindings prove the child budgets, and the original Gauss,
row and first-allowance identities pay the remaining scalar. The
common and newly frozen profiles cost their own two slot powers, while
`W.profileBound` remains a single factor. Any frozen scalar from the
preceding original allocation stays outside this calculation and must
be paid once on that original allocation.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum HeckeGeneral.Arithmetic
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section ExactPair

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (frozenL : left.source.FrozenAtomBounds) (frozenR : right.source.FrozenAtomBounds)
variable {IL : (left.arithmeticCalibration calL W frozenL).CapacityInput}
variable {IR : (right.arithmeticCalibration calR W frozenR).CapacityInput}
variable (lc : (left.arithmeticCalibration calL W frozenL).CapacityChild IL)
variable (rc : (right.arithmeticCalibration calR W frozenR).CapacityChild IR)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)

private theorem independent_sqrt_rpow_half (Z : ℝ) (hZ : 0 < Z) (x : ℝ) :
    Real.sqrt (Z ^ x) = Z ^ (x / 2) := by
  sorry

private theorem independent_sqrt_arithmetic_cost (q E F B N Z d : ℝ)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hZ : 0 < Z) :
    Real.sqrt ((q * (E / N) * F) * (B * Z ^ d)) =
      Real.sqrt q * Real.sqrt E * Real.sqrt F * Real.sqrt B * Z ^ (d / 2) / Real.sqrt N := by
  sorry

private theorem independent_pair_cost_identity
    (q EL ER F BL BR DL DR NL NR Z dL dR mL mR parent : ℝ)
    (hq : 0 ≤ q) (hEL : 0 ≤ EL) (hER : 0 ≤ ER) (hF : 0 ≤ F)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hDL : 0 ≤ DL) (hDR : 0 ≤ DR)
    (hZ : 0 < Z) :
    (Real.sqrt ((q * (EL / DL) * F) * (BL * Z ^ dL)) *
      Real.sqrt ((q * (ER / DR) * F) * (BR * Z ^ dR)) /
        (Real.sqrt NL * Real.sqrt NR)) * Z ^ ((mL + mR) / 2) / Z ^ parent =
      (F * Real.sqrt EL * Real.sqrt ER * Real.sqrt BL * Real.sqrt BR) /
        ((Real.sqrt DL * Real.sqrt DR) * Z ^ parent) *
      (q / (Real.sqrt NL * Real.sqrt NR) *
        Z ^ ((mL + mR + dL + dR) / 2)) := by
  sorry

/-- This identity holds for the actual capacity input, including the
full-deletion input.  It does not identify its changed coordinates with
the old ideal-log dictionary. -/
theorem actual_capacity_pair_weight_eq_original_row_independent
    (Z parentWidth : ℝ) (hZ : 0 < Z)
    (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i) :
    actualCapacityPairWeight left right calL calR W frozenL frozenR lc rc boundsL boundsR
        Z parentWidth =
      (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR /
        ((Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
          Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) * Z ^ parentWidth)) *
        (W.rowBound / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) *
          Z ^ ((lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q) +
            IL.exponent + IR.exponent) / 2)) := by
  sorry

/-- Internal scalar calculation.  The two child inequalities are
proved from the original sixth-root bindings below, not supplied by the
raw source or the public producer. -/
private theorem independent_pair_weight_le_from_child_budgets
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w krow g ell parentWidth slackL slackR : ℝ)
    (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hleft : lc.parameters.m + lc.parameters.q + IL.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g
        W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
      secondCommonChildAllowance Z w slackL ell W.leftIdeal W.rightIdeal)
    (hright : rc.parameters.m + rc.parameters.q + IR.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g
        W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
      secondCommonChildAllowance Z w slackR ell W.leftIdeal W.rightIdeal)
    (hscaleL : Z ^ a₀ ≤ left.normalizationScale)
    (hscaleR : Z ^ a₀ ≤ right.normalizationScale)
    (hradius : Z ^ (-krow - g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W frozenL frozenR lc rc boundsL boundsR
        Z parentWidth ≤
      (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR /
        ((Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
          Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) * Z ^ parentWidth)) *
      (W.commonEnvelope *
        (orbitalFieldFactor K * Z ^ (a₀ + q + w + (slackL + slackR) / 2) *
          Z ^ wo * Z ^ ell / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ))) := by
  sorry

end ExactPair

section OriginalSixthPair

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (frozenL : left.source.FrozenAtomBounds) (frozenR : right.source.FrozenAtomBounds)
variable (parent : MomentData K ω ψ) (a : RealParameters) (Z step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
variable (hn : ∀ i, 0 < R.rightMultiplicity i) (anchor : R.rows)
variable (hsecond : G.ideals.second.val = W.leftIdeal)
variable (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
variable (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
variable (hnonunit : G.ideals.nonunitPart.val = W.nonunitIdeal.val)
variable (bindingL : (left.arithmeticCalibration calL W frozenL).OriginalSixthLengthBinding
  parent a step (G.atBase left.source.base hbaseL)
  (idealLogLength left.source.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))
variable (bindingR : (right.arithmeticCalibration calR W frozenR).OriginalSixthLengthBinding
  parent a step (G.swapSecond.atBase right.source.base hbaseR)
  (idealLogLength right.source.base
    (secondSixthRootIdeal R.swapColumns.primes R.swapColumns.leftMultiplicity
      R.swapColumns.rightMultiplicity).val))
variable (atomsL : (left.arithmeticCalibration calL W frozenL).OriginalCapacityAtoms)
variable (atomsR : (right.arithmeticCalibration calR W frozenR).OriginalCapacityAtoms)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable (lc : (left.arithmeticCalibration calL W frozenL).CapacityChild
  (bindingL.capacityInput W hn anchor hsecond hopposite hunit hstep mesh hmesh hfit atomsL))
variable (rc : (right.arithmeticCalibration calR W frozenR).CapacityChild
  (bindingR.capacityInput (W.swapColumns hn) W.left_positive anchor
    hopposite hsecond hunit hstep mesh hmesh hfit atomsR))
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)

include hnonunit in
/-- The old second scalar is valid for these exact full-deletion
children.  The root is paid by `child_budget` before either side is
combined; no old norm-length record is constructed. -/
theorem actual_sixth_capacity_pair_weight_le_independent
    (hZ : 1 < Z) (parentWidth : ℝ)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W frozenL frozenR lc rc boundsL boundsR
        Z parentWidth ≤
      (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR /
        ((Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
          Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) * Z ^ parentWidth)) *
      (W.commonEnvelope * (orbitalFieldFactor K *
        Z ^ ((G.skeleton.A - G.skeleton.c - G.skeleton.w) +
          (G.skeleton.q + G.skeleton.R + G.skeleton.E) + G.skeleton.w +
          (bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2) *
        Z ^ G.skeleton.wo * Z ^ (G.tag.poolLength step) /
          (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ))) := by
  sorry

include hnonunit in
/-- Divide by the literal original first Cauchy allowance.  The
remaining power contains only the unchanged original slack and tag. -/
theorem actual_sixth_capacity_pair_relative_allowance_le_independent
    (hZ : 1 < Z) (parentWidth firstNormalization : ℝ)
    (hN : firstNormalization =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W frozenL frozenR lc rc boundsL boundsR
        Z parentWidth / firstNormalization ≤
      (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor K *
        Z ^ ((bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2 - G.boundary) *
        Z ^ G.skeleton.wo * Z ^ (G.tag.poolLength step) / Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
            Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) := by
  sorry

end OriginalSixthPair

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]

section NormalizedPair

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (frozenL : left.source.FrozenAtomBounds) (frozenR : right.source.FrozenAtomBounds)
variable (IL : (left.arithmeticCalibration calL W frozenL).CapacityInput)
variable (IR : (right.arithmeticCalibration calR W frozenR).CapacityInput)
variable (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * boundsR i)
variable (lc : (IL.normalized AL hAL boundsL hBL hfL).Child)
variable (rc : (IR.normalized AR hAR boundsR hBR hfR).Child)
variable (parent : MomentData K ω ψ) (a : RealParameters) (Z step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
variable (hn : ∀ i, 0 < R.rightMultiplicity i) (anchor : R.rows)
variable (hsecond : G.ideals.second.val = W.leftIdeal)
variable (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
variable (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
variable (hnonunit : G.ideals.nonunitPart.val = W.nonunitIdeal.val)
variable (bindingL : (left.arithmeticCalibration calL W frozenL).OriginalSixthLengthBinding
  parent a step (G.atBase left.source.base hbaseL)
  (idealLogLength left.source.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))
variable (bindingR : (right.arithmeticCalibration calR W frozenR).OriginalSixthLengthBinding
  parent a step (G.swapSecond.atBase right.source.base hbaseR)
  (idealLogLength right.source.base
    (secondSixthRootIdeal R.swapColumns.primes R.swapColumns.leftMultiplicity
      R.swapColumns.rightMultiplicity).val))
variable (atomsL : (left.arithmeticCalibration calL W frozenL).OriginalCapacityAtoms)
variable (atomsR : (right.arithmeticCalibration calR W frozenR).OriginalCapacityAtoms)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable (hIL : IL =
  bindingL.capacityInput W hn anchor hsecond hopposite hunit hstep mesh hmesh hfit atomsL)
variable (hIR : IR =
  bindingR.capacityInput (W.swapColumns hn) W.left_positive anchor
    hopposite hsecond hunit hstep mesh hmesh hfit atomsR)

include hnonunit hIL hIR in
/-- This is the actual normalized pair after full deletion.  The two
input equalities identify its existing capacity data; they do not select
new children or new removed sets.  Every scalar inequality is derived
from the original windows below. -/
theorem normalized_sixth_pair_original_allowance_independent
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hboundsL : boundsL = fun _ => 1) (hboundsR : boundsR = fun _ => 1)
    (hleft : k ≤ cap) (hright : l ≤ cap)
    (hcommonLeft : kLeft ≤ cap) (hcommonRight : kRight ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B)
    (hfrozenL : ∀ i ∈ Finset.univ \ left.source.allocation.keep,
      frozenL.annulus i * frozenL.profile i ≤ B)
    (hfrozenR : ∀ i ∈ Finset.univ \ right.source.allocation.keep,
      frozenR.annulus i * frozenR.profile i ≤ B)
    (firstNormalization : ℝ)
    (hN : firstNormalization =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (annulus error : ℝ) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z 0 /
        firstNormalization ≤
      ((W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) * orbitalFieldFactor K) *
        Z ^ (G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh) *
          (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
            (Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
              Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) := by
  sorry

end NormalizedPair

section OriginalAllocation

variable {k₀ l₀ : ℕ}
variable (originalLeft : ActualAllocatedSource A V H k₀)
variable (originalRight : ActualAllocatedSource A V H l₀)
variable (originalFrozenL : originalLeft.FrozenAtomBounds)
variable (originalFrozenR : originalRight.FrozenAtomBounds)

private theorem original_frozen_envelope_le
    {j : ℕ} {source : ActualAllocatedSource A V H j}
    (F : source.FrozenAtomBounds) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hcap : j ≤ cap)
    (hslot : ∀ i ∈ Finset.univ \ source.allocation.keep, F.annulus i * F.profile i ≤ B) :
    F.envelope ≤ B ^ cap := by
  sorry

/-- The preceding original allocation's scalar is kept separate from
the new passive allocation. This is its exact pair of norm divisors. -/
theorem original_frozen_pair_eq_independent :
    Real.sqrt originalFrozenL.scalarBound * Real.sqrt originalFrozenR.scalarBound =
      (Real.sqrt originalFrozenL.envelope * Real.sqrt originalFrozenR.envelope) /
        (Real.sqrt (Ideal.absNorm originalLeft.allocation.divisor : ℝ) *
          Real.sqrt (Ideal.absNorm originalRight.allocation.divisor : ℝ)) := by
  sorry

/-- One further slot power pays this whole original frozen pair.
It is not inserted into a profile radius or charged once per new slot. -/
theorem original_frozen_pair_le_independent
    (cap : ℕ) (B : ℝ) (hB : 1 ≤ B) (hleft : k₀ ≤ cap) (hright : l₀ ≤ cap)
    (hslotL : ∀ i ∈ Finset.univ \ originalLeft.allocation.keep,
      originalFrozenL.annulus i * originalFrozenL.profile i ≤ B)
    (hslotR : ∀ i ∈ Finset.univ \ originalRight.allocation.keep,
      originalFrozenR.annulus i * originalFrozenR.profile i ≤ B) :
    Real.sqrt originalFrozenL.scalarBound * Real.sqrt originalFrozenR.scalarBound ≤
      B ^ cap / (Real.sqrt (Ideal.absNorm originalLeft.allocation.divisor : ℝ) *
        Real.sqrt (Ideal.absNorm originalRight.allocation.divisor : ℝ)) := by
  sorry

/-- This common-divisor identity belongs only to the preceding
original allocation. The later two passive divisors remain independent. -/
theorem original_frozen_pair_le_shared_norm
    (cap : ℕ) (B : ℝ) (hB : 1 ≤ B) (hleft : k₀ ≤ cap) (hright : l₀ ≤ cap)
    (hslotL : ∀ i ∈ Finset.univ \ originalLeft.allocation.keep,
      originalFrozenL.annulus i * originalFrozenL.profile i ≤ B)
    (hslotR : ∀ i ∈ Finset.univ \ originalRight.allocation.keep,
      originalFrozenR.annulus i * originalFrozenR.profile i ≤ B)
    (horiginalDivisor : originalLeft.allocation.divisor = originalRight.allocation.divisor) :
    Real.sqrt originalFrozenL.scalarBound * Real.sqrt originalFrozenR.scalarBound ≤
      B ^ cap / (Ideal.absNorm originalLeft.allocation.divisor : ℝ) := by
  sorry

/-- The literal original frozen scalars satisfy this bound from their
individual arithmetic and profile windows. No scalar estimate is an
input, and the old divisor cost occurs exactly once. -/
theorem original_allocation_scalar_pair_le_shared_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (cap : ℕ) (B : ℝ) (hB : 1 ≤ B) (hleft : k₀ ≤ cap) (hright : l₀ ≤ cap)
    (hslotL : ∀ i ∈ Finset.univ \ originalLeft.allocation.keep,
      originalFrozenL.annulus i * originalFrozenL.profile i ≤ B)
    (hslotR : ∀ i ∈ Finset.univ \ originalRight.allocation.keep,
      originalFrozenR.annulus i * originalFrozenR.profile i ≤ B)
    (horiginalDivisor : originalLeft.allocation.divisor = originalRight.allocation.divisor)
    (h : H) (hhL : h ∈ originalLeft.rows) (hhR : h ∈ originalRight.rows) :
    ‖originalLeft.frozenScalar (σ := σ) h‖ * ‖originalRight.frozenScalar (σ := σ) h‖ ≤
      B ^ cap / (Ideal.absNorm originalLeft.allocation.divisor : ℝ) := by
  sorry

end OriginalAllocation
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_weight_eq_original_row_independent
#print axioms HeckeSkeleton.Moments.EngineStep.actual_sixth_capacity_pair_weight_le_independent
#print axioms HeckeSkeleton.Moments.EngineStep.actual_sixth_capacity_pair_relative_allowance_le_independent
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_sixth_pair_original_allowance_independent
#print axioms HeckeSkeleton.Moments.EngineStep.original_frozen_pair_eq_independent
#print axioms HeckeSkeleton.Moments.EngineStep.original_frozen_pair_le_independent
#print axioms HeckeSkeleton.Moments.EngineStep.original_frozen_pair_le_shared_norm
#print axioms HeckeSkeleton.Moments.EngineStep.original_allocation_scalar_pair_le_shared_norm
