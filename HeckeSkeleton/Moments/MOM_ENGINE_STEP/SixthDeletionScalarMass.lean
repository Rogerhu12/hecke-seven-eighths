import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalPairAllowance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondRowMassSwap

/-!
# The same full-deletion children pay the original scalar

The actual support includes the complete sixth-root ideal.  Its logarithmic
norm is added to the support width and subtracted from the capacity allowance.
Consequently the old norm-length record is not an input: its unit and common
coordinates would be false for these children.

The exact arithmetic cost is instead expanded for the same chosen children.
The proved full-deletion child budget then cancels the root before the original
row scalar estimate is applied.  Both Gauss normalizers, the original row
fibre, all removed prime costs and the independent second divisor remain.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum HeckeGeneral.Arithmetic
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ActualAllocatedSource.Calibration.OriginalSixthLengthBinding

variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ}
variable {parent : MomentData K ω ψ} {a : RealParameters} {step rootLength : ℝ}
variable {G : OriginalNominalGeometry (K := K) a s.base step}
variable (B : D.OriginalSixthLengthBinding parent a step G rootLength)

/-- The root introduces no hidden slack.  This is the original annulus,
support, raw clipping, width and mesh calculation on the same calibration. -/
theorem massSlack_le_original_windows
    (mesh : ℝ) (hmesh : 0 ≤ mesh) (atoms : D.OriginalCapacityAtoms)
    (annulus error : ℝ) (herror : 0 < error)
    (hZ : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ s.base)
    (hleft : atoms.leftAnnulus ≤ annulus) (hright : atoms.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error) (hraw : B.rawScaleError ≤ error)
    (hwidth : B.scales.error ≤ error) :
    B.massSlack mesh atoms ≤ G.boundary + 5 * error / 3 + mesh := by
  have hannulus := OriginalPairAllowanceProduction.annulus_error_le
    annulus error s.base atoms.leftAnnulus atoms.rightAnnulus herror hZ
    atoms.leftAnnulus_one hleft atoms.rightAnnulus_one hright
  have hkappa : D.parameters.κ ≤ 1 := by
    rw [B.kappa]
    exact B.parent_region.2.1
  have hovershoot : D.parameters.κ * mesh ≤ mesh := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hkappa hmesh
  unfold massSlack
  linarith

end ActualAllocatedSource.Calibration.OriginalSixthLengthBinding

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

private theorem sixth_sqrt_rpow_half (Z : ℝ) (hZ : 0 < Z) (x : ℝ) :
    Real.sqrt (Z ^ x) = Z ^ (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
  congr 1
  ring

private theorem sixth_sqrt_arithmetic_cost (q E F B N Z d : ℝ)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hZ : 0 < Z) :
    Real.sqrt ((q * (E / N) * F) * (B * Z ^ d)) =
      Real.sqrt q * Real.sqrt E * Real.sqrt F * Real.sqrt B * Z ^ (d / 2) / Real.sqrt N := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hq (div_nonneg hE hN)) hF),
    Real.sqrt_mul (mul_nonneg hq (div_nonneg hE hN)),
    Real.sqrt_mul hq, Real.sqrt_mul hB, Real.sqrt_div hE,
    sixth_sqrt_rpow_half Z hZ]
  ring

private theorem sixth_pair_cost_identity
    (q EL ER F BL BR N NL NR Z dL dR mL mR parent : ℝ)
    (hq : 0 ≤ q) (hEL : 0 ≤ EL) (hER : 0 ≤ ER) (hF : 0 ≤ F)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hN : 0 ≤ N) (hZ : 0 < Z) :
    (Real.sqrt ((q * (EL / N) * F) * (BL * Z ^ dL)) *
      Real.sqrt ((q * (ER / N) * F) * (BR * Z ^ dR)) /
        (Real.sqrt NL * Real.sqrt NR)) * Z ^ ((mL + mR) / 2) / Z ^ parent =
      (F * Real.sqrt EL * Real.sqrt ER * Real.sqrt BL * Real.sqrt BR) /
        (N * Z ^ parent) *
      (q / (Real.sqrt NL * Real.sqrt NR) *
        Z ^ ((mL + mR + dL + dR) / 2)) := by
  rw [sixth_sqrt_arithmetic_cost q EL F BL N Z dL hq hEL hF hBL hN hZ,
    sixth_sqrt_arithmetic_cost q ER F BR N Z dR hq hER hF hBR hN hZ]
  have hq₂ : Real.sqrt q * Real.sqrt q = q := by nlinarith [Real.sq_sqrt hq]
  have hF₂ : Real.sqrt F * Real.sqrt F = F := by nlinarith [Real.sq_sqrt hF]
  have hN₂ : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = N⁻¹ := by
    rw [← mul_inv]
    congr 1
    nlinarith [Real.sq_sqrt hN]
  have hp : Z ^ (dL / 2) * Z ^ (dR / 2) * Z ^ ((mL + mR) / 2) =
      Z ^ ((mL + mR + dL + dR) / 2) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (Real.sqrt q * Real.sqrt q) * (Real.sqrt F * Real.sqrt F) *
        (Real.sqrt EL * Real.sqrt ER * Real.sqrt BL * Real.sqrt BR) *
        ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) *
        ((Real.sqrt NR)⁻¹ * (Real.sqrt NL)⁻¹) *
        (Z ^ (dL / 2) * Z ^ (dR / 2) * Z ^ ((mL + mR) / 2)) * (Z ^ parent)⁻¹ := by ring
    _ = _ := by rw [hq₂, hF₂, hN₂, hp]; ring

/-- This identity holds for the actual capacity input, including the
full-deletion input.  It does not identify its changed coordinates with
the old ideal-log dictionary. -/
theorem actual_capacity_pair_weight_eq_original_row
    (Z parentWidth : ℝ) (hZ : 0 < Z)
    (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor) :
    actualCapacityPairWeight left right calL calR W frozenL frozenR lc rc boundsL boundsR
        Z parentWidth =
      (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) * Z ^ parentWidth)) *
        (W.rowBound / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) *
          Z ^ ((lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q) +
            IL.exponent + IR.exponent) / 2)) := by
  unfold actualCapacityPairWeight actualCapacityPairEnvelope
  rw [left.arithmetic_child_cost calL W frozenL lc boundsL,
    right.arithmetic_child_cost calR W frozenR rc boundsR, hbaseL, hbaseR, ← hdivisor]
  exact sixth_pair_cost_identity W.rowBound frozenL.envelope frozenR.envelope (W.originalFiber : ℝ)
    (∏ i ∈ lc.removed, boundsL i) (∏ i ∈ rc.removed, boundsR i)
    (Ideal.absNorm left.source.allocation.divisor : ℝ)
    left.normalizationScale right.normalizationScale Z IL.exponent IR.exponent
    (lc.parameters.m + lc.parameters.q) (rc.parameters.m + rc.parameters.q) parentWidth
    W.rowBound_nonneg frozenL.envelope_nonneg frozenR.envelope_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ => hBL i) (Finset.prod_nonneg fun i _ => hBR i)
    frozenL.divisorNorm_pos.le hZ

/-- Internal scalar calculation.  The two child inequalities are
proved from the original sixth-root bindings below, not supplied by the
raw source or the public producer. -/
private theorem sixth_pair_weight_le_from_child_budgets
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w krow g ell parentWidth slackL slackR : ℝ)
    (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
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
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) * Z ^ parentWidth)) *
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
  rw [actual_capacity_pair_weight_eq_original_row left right calL calR W frozenL frozenR
    lc rc boundsL boundsR Z parentWidth hz hbaseL hbaseR hBL hBR hdivisor]
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (actualCapacityPairEnvelope_nonneg left right calL calR W frozenL frozenR
      lc rc boundsL boundsR) (mul_nonneg frozenL.divisorNorm_pos.le (Real.rpow_nonneg hz.le _)))
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
theorem actual_sixth_capacity_pair_weight_le
    (hZ : 1 < Z) (parentWidth : ℝ)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    actualCapacityPairWeight left right calL calR W frozenL frozenR lc rc boundsL boundsR
        Z parentWidth ≤
      (actualCapacityPairEnvelope left right calL calR W frozenL frozenR lc rc boundsL boundsR /
        ((Ideal.absNorm left.source.allocation.divisor : ℝ) * Z ^ parentWidth)) *
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
  simp only [OriginalNominalGeometry.atBase_skeleton] at hl
  change lc.parameters.m + lc.parameters.q +
      (bindingL.capacityInput W hn anchor hsecond hopposite hunit
        hstep mesh hmesh hfit atomsL).exponent ≤
    secondCommonChildWidth left.source.base
      (G.skeleton.A - G.skeleton.c - G.skeleton.w)
      (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
      G.skeleton.Krow G.skeleton.g G.ideals.second.val G.ideals.secondOpposite.val
      G.ideals.unitPart.val G.ideals.nonunitPart.val +
    secondCommonChildAllowance left.source.base G.skeleton.w (bindingL.massSlack mesh atomsL)
      (G.tag.poolLength step) G.ideals.second.val G.ideals.secondOpposite.val at hl
  simp only [hbaseL, hsecond, hopposite, hunit, hnonunit] at hl
  simp only [OriginalNominalGeometry.atBase_skeleton,
    OriginalNominalGeometry.swapSecond_skeleton] at hr
  change rc.parameters.m + rc.parameters.q +
      (bindingR.capacityInput (W.swapColumns hn) W.left_positive anchor
        hopposite hsecond hunit hstep mesh hmesh hfit atomsR).exponent ≤
    secondCommonChildWidth right.source.base
      (G.skeleton.A - G.skeleton.c - G.skeleton.w)
      (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
      G.skeleton.Krow G.skeleton.g G.ideals.secondOpposite.val G.ideals.second.val
      G.ideals.unitPart.val G.ideals.nonunitPart.val +
    secondCommonChildAllowance right.source.base G.skeleton.w (bindingR.massSlack mesh atomsR)
      (G.tag.poolLength step) G.ideals.secondOpposite.val G.ideals.second.val at hr
  simp only [hbaseR, hsecond, hopposite, hunit, hnonunit] at hr
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
  exact sixth_pair_weight_le_from_child_budgets left right calL calR W frozenL frozenR
    lc rc boundsL boundsR Z hZ
    (G.skeleton.A - G.skeleton.c - G.skeleton.w)
    (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo G.skeleton.w
    G.skeleton.Krow G.skeleton.g (G.tag.poolLength step) parentWidth
    (bindingL.massSlack mesh atomsL) (bindingR.massSlack mesh atomsR)
    hbaseL hbaseR hBL hBR hdivisor hl hr hscaleL hscaleR hradius

include hnonunit in
/-- Divide by the literal original first Cauchy allowance.  The
remaining power contains only the unchanged original slack and tag. -/
theorem actual_sixth_capacity_pair_relative_allowance_le
    (hZ : 1 < Z) (parentWidth firstNormalization : ℝ)
    (hN : firstNormalization =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
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
          (Ideal.absNorm left.source.allocation.divisor : ℝ) := by
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
  have h := actual_sixth_capacity_pair_weight_le left right calL calR W frozenL frozenR
    parent a Z step G hbaseL hbaseR hn anchor hsecond hopposite hunit hnonunit
    bindingL bindingR atomsL atomsR hstep mesh hmesh hfit lc rc boundsL boundsR
    hZ parentWidth hBL hBR hdivisor hscaleL hscaleR hradius
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
          (Ideal.absNorm left.source.allocation.divisor : ℝ) := by ring
    _ = _ := by rw [hcancel]

end OriginalSixthPair

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.massSlack_le_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_weight_eq_original_row
#print axioms HeckeSkeleton.Moments.EngineStep.actual_sixth_capacity_pair_relative_allowance_le
