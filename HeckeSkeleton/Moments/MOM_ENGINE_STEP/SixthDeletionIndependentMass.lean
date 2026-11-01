import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionSeparateMass

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
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
  congr 1
  ring

private theorem independent_sqrt_arithmetic_cost (q E F B N Z d : ℝ)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hZ : 0 < Z) :
    Real.sqrt ((q * (E / N) * F) * (B * Z ^ d)) =
      Real.sqrt q * Real.sqrt E * Real.sqrt F * Real.sqrt B * Z ^ (d / 2) / Real.sqrt N := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hq (div_nonneg hE hN)) hF),
    Real.sqrt_mul (mul_nonneg hq (div_nonneg hE hN)),
    Real.sqrt_mul hq, Real.sqrt_mul hB, Real.sqrt_div hE,
    independent_sqrt_rpow_half Z hZ]
  ring

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
  rw [independent_sqrt_arithmetic_cost q EL F BL DL Z dL hq hEL hF hBL hDL hZ,
    independent_sqrt_arithmetic_cost q ER F BR DR Z dR hq hER hF hBR hDR hZ]
  have hq₂ : Real.sqrt q * Real.sqrt q = q := by nlinarith [Real.sq_sqrt hq]
  have hF₂ : Real.sqrt F * Real.sqrt F = F := by nlinarith [Real.sq_sqrt hF]
  have hp : Z ^ (dL / 2) * Z ^ (dR / 2) * Z ^ ((mL + mR) / 2) =
      Z ^ ((mL + mR + dL + dR) / 2) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (Real.sqrt q * Real.sqrt q) * (Real.sqrt F * Real.sqrt F) *
        (Real.sqrt EL * Real.sqrt ER * Real.sqrt BL * Real.sqrt BR) *
        ((Real.sqrt DR)⁻¹ * (Real.sqrt DL)⁻¹) *
        ((Real.sqrt NR)⁻¹ * (Real.sqrt NL)⁻¹) *
        (Z ^ (dL / 2) * Z ^ (dR / 2) * Z ^ ((mL + mR) / 2)) * (Z ^ parent)⁻¹ := by ring
    _ = _ := by rw [hq₂, hF₂, hp]; ring

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
  unfold actualCapacityPairWeight actualCapacityPairEnvelope
  rw [left.arithmetic_child_cost calL W frozenL lc boundsL,
    right.arithmetic_child_cost calR W frozenR rc boundsR, hbaseL, hbaseR]
  exact independent_pair_cost_identity W.rowBound frozenL.envelope frozenR.envelope
    (W.originalFiber : ℝ) (∏ i ∈ lc.removed, boundsL i) (∏ i ∈ rc.removed, boundsR i)
    (Ideal.absNorm left.source.allocation.divisor : ℝ)
    (Ideal.absNorm right.source.allocation.divisor : ℝ)
    left.normalizationScale right.normalizationScale Z IL.exponent IR.exponent
    (lc.parameters.m + lc.parameters.q) (rc.parameters.m + rc.parameters.q) parentWidth
    W.rowBound_nonneg frozenL.envelope_nonneg frozenR.envelope_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ => hBL i) (Finset.prod_nonneg fun i _ => hBR i)
    frozenL.divisorNorm_pos.le frozenR.divisorNorm_pos.le hZ

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
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcentral := second_source_central_scale_lower Z hz a₀
    left.normalizationScale right.normalizationScale hscaleL hscaleR
  have hexp :
      (lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q) +
        IL.exponent + IR.exponent) / 2 ≤
      secondCommonChildWidth Z a₀ q wo krow g
        W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
      secondCommonChildAllowance Z w ((slackL + slackR) / 2) ell W.leftIdeal W.rightIdeal := by
    unfold secondCommonChildAllowance at *
    linarith
  have hbudget := W.normalized_row_budget Z hZ a₀ q wo w ((slackL + slackR) / 2)
    krow g ell left.normalizationScale right.normalizationScale hradius hcentral
  rw [actual_capacity_pair_weight_eq_original_row_independent left right calL calR W frozenL frozenR
    lc rc boundsL boundsR Z parentWidth hz hbaseL hbaseR hBL hBR]
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (actualCapacityPairEnvelope_nonneg left right calL calR W frozenL frozenR
      lc rc boundsL boundsR) (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg hz.le _)))
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
    (div_nonneg W.rowBound_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).trans
      hbudget

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
  have hl := bindingL.child_budget W hn anchor hsecond hopposite hunit
    hstep mesh hmesh hfit atomsL lc
  have hr := bindingR.child_budget (W.swapColumns hn) W.left_positive anchor
    hopposite hsecond hunit hstep mesh hmesh hfit atomsR rc
  simp only [OriginalNominalGeometry.atBase_skeleton, hbaseL,
    hsecond, hopposite, hunit, hnonunit] at hl
  simp only [OriginalNominalGeometry.atBase_skeleton,
    OriginalNominalGeometry.swapSecond_skeleton, hbaseR,
    OriginalNominalGeometry.atBase, OriginalNominalGeometry.swapSecond,
    OriginalNominalIdeals.swapSecond, hsecond, hopposite, hunit, hnonunit] at hr
  have hwidthSwap :
      secondCommonChildWidth Z
        (G.skeleton.A - G.skeleton.c - G.skeleton.w)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g W.rightIdeal W.leftIdeal
        W.unitIdeal.val W.nonunitIdeal.val =
      secondCommonChildWidth Z
        (G.skeleton.A - G.skeleton.c - G.skeleton.w)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g W.leftIdeal W.rightIdeal
        W.unitIdeal.val W.nonunitIdeal.val := by
    unfold secondCommonChildWidth
    rw [gcd_comm W.rightIdeal W.leftIdeal]
  have hallowanceSwap :
      secondCommonChildAllowance Z G.skeleton.w (bindingR.massSlack mesh atomsR)
        (G.tag.poolLength step) W.rightIdeal W.leftIdeal =
      secondCommonChildAllowance Z G.skeleton.w (bindingR.massSlack mesh atomsR)
        (G.tag.poolLength step) W.leftIdeal W.rightIdeal := by
    unfold secondCommonChildAllowance commonRadical
    rw [Finset.inter_comm (primeSupport W.rightIdeal) (primeSupport W.leftIdeal),
      add_comm (idealLogLength Z W.rightIdeal) (idealLogLength Z W.leftIdeal)]
  rw [hwidthSwap, hallowanceSwap] at hr
  exact independent_pair_weight_le_from_child_budgets left right calL calR W frozenL frozenR
    lc rc boundsL boundsR Z hZ
    (G.skeleton.A - G.skeleton.c - G.skeleton.w)
    (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo G.skeleton.w
    G.skeleton.Krow G.skeleton.g (G.tag.poolLength step) parentWidth
    (bindingL.massSlack mesh atomsL) (bindingR.massSlack mesh atomsR)
    hbaseL hbaseR hBL hBR hl hr hscaleL hscaleR hradius

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
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hNpower : firstNormalization =
      Z ^ ((G.skeleton.A - G.skeleton.c - G.skeleton.w) +
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) + G.skeleton.w + G.boundary) := by
    rw [hN]
    exact firstLeftAllowance_second_exponent Z G.skeleton.A
      (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.w
      G.ideals.first.val G.ideals.opposite.val
  have hNpos : 0 < firstNormalization := by
    rw [hNpower]
    exact Real.rpow_pos_of_pos hz _
  have hcancel :
      Z ^ ((G.skeleton.A - G.skeleton.c - G.skeleton.w) +
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) + G.skeleton.w +
        (bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2) /
        firstNormalization =
      Z ^ ((bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2 - G.boundary) := by
    rw [hNpower, ← Real.rpow_sub hz]
    congr 1
    ring
  have h := actual_sixth_capacity_pair_weight_le_independent left right calL calR W frozenL frozenR
    parent a Z step G hbaseL hbaseR hn anchor hsecond hopposite hunit hnonunit
    bindingL bindingR atomsL atomsR hstep mesh hmesh hfit lc rc boundsL boundsR
    hZ parentWidth hBL hBR hscaleL hscaleR hradius
  apply (div_le_div_of_nonneg_right h hNpos.le).trans_eq
  calc
    _ = (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor K *
        (Z ^ ((G.skeleton.A - G.skeleton.c - G.skeleton.w) +
          (G.skeleton.q + G.skeleton.R + G.skeleton.E) + G.skeleton.w +
          (bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2) /
          firstNormalization) * Z ^ G.skeleton.wo * Z ^ (G.tag.poolLength step) /
          Z ^ parentWidth) *
        (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
          (Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
            Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) := by ring
    _ = _ := by rw [hcancel]

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
  have hz : 0 < Z := zero_lt_one.trans hZ
  let rawL := IL.rawChild AL hAL boundsL hBL hfL lc
  let rawR := IR.rawChild AR hAR boundsR hBR hfR rc
  have hraw :
      actualCapacityPairWeight left right calL calR W frozenL frozenR rawL rawR boundsL boundsR
          Z 0 / firstNormalization ≤
        (actualCapacityPairEnvelope left right calL calR W frozenL frozenR rawL rawR boundsL boundsR *
          W.commonEnvelope * orbitalFieldFactor K *
          Z ^ ((bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2 - G.boundary) *
          Z ^ G.skeleton.wo * Z ^ (G.tag.poolLength step) / Z ^ (0 : ℝ)) *
          (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
            (Real.sqrt (Ideal.absNorm left.source.allocation.divisor : ℝ) *
              Real.sqrt (Ideal.absNorm right.source.allocation.divisor : ℝ)) := by
    subst IL
    subst IR
    exact actual_sixth_capacity_pair_relative_allowance_le_independent left right calL calR W frozenL frozenR
      parent a Z step G hbaseL hbaseR hn anchor hsecond hopposite hunit hnonunit
      bindingL bindingR atomsL atomsR hstep mesh hmesh hfit rawL rawR boundsL boundsR
      hZ 0 firstNormalization hN hBL hBR hscaleL hscaleR hradius
  have hsl : bindingL.massSlack mesh atomsL ≤ G.boundary + 5 * error / 3 + mesh := by
    simpa only [OriginalNominalGeometry.atBase_boundary] using
      bindingL.massSlack_le_original_windows mesh hmesh atomsL annulus error herror
        (by simpa only [hbaseL] using hthreshold) hannulusLL hannulusLR hsupport hrawL hwidthL
  have hsr : bindingR.massSlack mesh atomsR ≤ G.boundary + 5 * error / 3 + mesh := by
    simpa only [OriginalNominalGeometry.atBase_boundary,
      OriginalNominalGeometry.swapSecond_boundary] using
      bindingR.massSlack_le_original_windows mesh hmesh atomsR annulus error herror
        (by simpa only [hbaseR] using hthreshold) hannulusRL hannulusRR hsupport hrawR hwidthR
  have hmargin :
      (bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2 - G.boundary +
        G.skeleton.wo + G.tag.poolLength step ≤
      G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh := by linarith
  have hatoms :
      actualCapacityPairEnvelope left right calL calR W frozenL frozenR rawL rawR boundsL boundsR *
        W.commonEnvelope ≤ (W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) := by
    simpa only [hboundsL, hboundsR] using
      CanonicalSeparateAtomMass.pairEnvelope_mul_common_le_one
        left right calL calR W frozenL frozenR rawL rawR cap B hB
        hleft hright hcommonLeft hcommonRight hcommonL hcommonR hfrozenL hfrozenR
  have hconstant : 0 ≤ (W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) * orbitalFieldFactor K :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) W.profileBound_nonneg)
        (pow_nonneg (zero_le_one.trans hB) _))
      (orbitalFieldFactor_nonneg K)
  have hscalar :
      actualCapacityPairEnvelope left right calL calR W frozenL frozenR rawL rawR boundsL boundsR *
        W.commonEnvelope * orbitalFieldFactor K *
        Z ^ ((bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2 - G.boundary) *
        Z ^ G.skeleton.wo * Z ^ (G.tag.poolLength step) / Z ^ (0 : ℝ) ≤
      ((W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) * orbitalFieldFactor K) *
        Z ^ (G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh) := by
    calc
      _ = (actualCapacityPairEnvelope left right calL calR W frozenL frozenR rawL rawR boundsL boundsR *
          W.commonEnvelope * orbitalFieldFactor K) *
          Z ^ ((bindingL.massSlack mesh atomsL + bindingR.massSlack mesh atomsR) / 2 - G.boundary +
            G.skeleton.wo + G.tag.poolLength step) := by
        rw [Real.rpow_zero, div_one, Real.rpow_add hz, Real.rpow_add hz]
        ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hatoms (orbitalFieldFactor_nonneg K))
        (Real.rpow_le_rpow_of_exponent_le hZ.le hmargin)
        (Real.rpow_nonneg hz.le _) hconstant
  rw [normalized_pair_weight_eq_canonical left right calL calR W frozenL frozenR IL IR
    AL AR hAL hAR boundsL boundsR hBL hBR hfL hfR lc rc Z 0 hz]
  exact hraw.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscalar (one_div_nonneg.mpr (Nat.cast_nonneg _)))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

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
  calc
    _ ≤ ∏ _i ∈ Finset.univ \ source.allocation.keep, B :=
      Finset.prod_le_prod₀
        (fun i _ => mul_nonneg (F.annulus_nonneg i) (F.profile_nonneg i)) hslot
    _ = B ^ (Finset.univ \ source.allocation.keep).card := Finset.prod_const B
    _ ≤ _ := pow_le_pow_right₀ hB ((Finset.card_le_univ _).trans
      (by simpa only [Fintype.card_fin] using hcap))

/-- The preceding original allocation's scalar is kept separate from
the new passive allocation. This is its exact pair of norm divisors. -/
theorem original_frozen_pair_eq_independent :
    Real.sqrt originalFrozenL.scalarBound * Real.sqrt originalFrozenR.scalarBound =
      (Real.sqrt originalFrozenL.envelope * Real.sqrt originalFrozenR.envelope) /
        (Real.sqrt (Ideal.absNorm originalLeft.allocation.divisor : ℝ) *
          Real.sqrt (Ideal.absNorm originalRight.allocation.divisor : ℝ)) := by
  rw [ActualAllocatedSource.FrozenAtomBounds.scalarBound,
    ActualAllocatedSource.FrozenAtomBounds.scalarBound,
    Real.sqrt_div originalFrozenL.envelope_nonneg,
    Real.sqrt_div originalFrozenR.envelope_nonneg, div_mul_div_comm]

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
  rw [original_frozen_pair_eq_independent originalLeft originalRight originalFrozenL originalFrozenR]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ ≤ Real.sqrt (B ^ cap) * Real.sqrt (B ^ cap) :=
      mul_le_mul
        (Real.sqrt_le_sqrt (original_frozen_envelope_le originalFrozenL cap B hB hleft hslotL))
        (Real.sqrt_le_sqrt (original_frozen_envelope_le originalFrozenR cap B hB hright hslotR))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (pow_nonneg (zero_le_one.trans hB) cap)

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
  have h := original_frozen_pair_le_independent originalLeft originalRight
    originalFrozenL originalFrozenR cap B hB hleft hright hslotL hslotR
  simpa only [← horiginalDivisor, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

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
  have hl : ‖originalLeft.frozenScalar (σ := σ) h‖ ≤ Real.sqrt originalFrozenL.scalarBound := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using
      Real.sqrt_le_sqrt (originalFrozenL.scalar_bound C h hhL)
  have hr : ‖originalRight.frozenScalar (σ := σ) h‖ ≤ Real.sqrt originalFrozenR.scalarBound := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using
      Real.sqrt_le_sqrt (originalFrozenR.scalar_bound C h hhR)
  exact (mul_le_mul hl hr (norm_nonneg _) (Real.sqrt_nonneg _)).trans
    (original_frozen_pair_le_shared_norm originalLeft originalRight originalFrozenL
      originalFrozenR cap B hB hleft hright hslotL hslotR horiginalDivisor)

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
