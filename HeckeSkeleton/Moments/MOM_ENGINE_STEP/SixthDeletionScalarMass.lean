import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalPairAllowance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondRowMassSwap

set_option linter.unusedSectionVars false

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
  sorry

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
  sorry

private theorem sixth_sqrt_arithmetic_cost (q E F B N Z d : ℝ)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hN : 0 ≤ N) (hZ : 0 < Z) :
    Real.sqrt ((q * (E / N) * F) * (B * Z ^ d)) =
      Real.sqrt q * Real.sqrt E * Real.sqrt F * Real.sqrt B * Z ^ (d / 2) / Real.sqrt N := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end OriginalSixthPair

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.massSlack_le_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_capacity_pair_weight_eq_original_row
#print axioms HeckeSkeleton.Moments.EngineStep.actual_sixth_capacity_pair_relative_allowance_le
