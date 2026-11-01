import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointNormalizedLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization

/-!
# Joint row budgets from the original separate norm windows

The original frequency window and the norm window of the same moving
support are multiplied before the actual extraction norm is cancelled.
All real exponents may be negative. The second-transform specialization
uses the genuine gcd and nonunit radical and an individual ideal
divisibility for the moving mask. It never assumes the final child row
budget or an aggregate source estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.CenteredMomentCounting CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}

/-- This uses only positivity of the base, not signs of either exponent. -/
theorem joint_row_product_of_separate_windows
    {Z original moving factor m q : ℝ}
    (hZ : 0 < Z) (hfactor : 0 ≤ factor) (hmoving : 0 ≤ moving)
    (hrow : original ≤ factor * Z ^ m) (hmask : moving ≤ Z ^ q) :
    original * moving ≤ factor * Z ^ (m + q) := by
  calc
    original * moving ≤ (factor * Z ^ m) * Z ^ q :=
      mul_le_mul hrow hmask hmoving
        (mul_nonneg hfactor (Real.rpow_nonneg hZ.le _))
    _ = factor * Z ^ (m + q) := by rw [Real.rpow_add hZ]; ring

theorem ActualChildRow.joint_norm_le_of_windows
    {Ih : A.Exterior} {h g : A.R} {Q : ℝ}
    (r : ActualChildRow Ih h g Q) (moving : A.Exterior)
    (Z m q : ℝ) (hZ : 0 < Z)
    (hrow : A.exteriorNorm Ih ≤ Q * Z ^ m)
    (hmask : A.exteriorNorm moving ≤ Z ^ q) :
    idealNorm K r.momentIdeal * A.exteriorNorm moving ≤ Z ^ (m + q) :=
  r.joint_norm_le moving _ (joint_row_product_of_separate_windows hZ
    r.factor_pos.le (Nat.cast_nonneg (Ideal.absNorm moving.val)) hrow hmask)

namespace ActualAllocatedSource.Calibration

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}
variable {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ)
variable (M : ActualMovingMaskRecipe A D.data)

/-- Only separate original frequency and actual support norm windows
are stored. Their product budget is a theorem. -/
structure RowWindows : Prop where
  original : ∀ h ∈ s.rows,
    A.exteriorNorm (s.originalIdeal h) ≤ s.normFactor h * s.base ^ D.parameters.m
  moving : ∀ h ∈ s.rows,
    A.exteriorNorm (M.support (s.row h).momentIdeal) ≤ s.base ^ D.parameters.q

theorem RowWindows.source_budget (W : D.RowWindows M) (h : H) (hh : h ∈ s.rows) :
    A.exteriorNorm (s.originalIdeal h) *
      A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
        s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q) :=
  joint_row_product_of_separate_windows (zero_lt_one.trans s.base_gt_one)
    (s.row h).factor_pos.le
    (Nat.cast_nonneg (Ideal.absNorm (M.support (s.row h).momentIdeal).val))
    (W.original h hh) (W.moving h hh)

def withJointRowWindows (W : D.RowWindows M) : s.Calibration (σ := σ) ω ψ :=
  D.withJointRowBudget M W.source_budget

theorem energy_le_withJointRowWindows (W : D.RowWindows M) (ξ : V) :
    s.energy (σ := σ) ξ ≤ D.mass *
      pairedEnergy ((D.withJointRowWindows M W).data ξ)
        D.parameters s.base (D.height ξ) :=
  D.energy_le_withJointRowBudget M W.source_budget ξ

end ActualAllocatedSource.Calibration

/-- Actual ideal logarithms cancel both extracted norm factors. -/
theorem extraction_norm_rpow_window
    (Z : ℝ) (hZ : 1 < Z) (x : ℝ)
    (G V : Ideal (𝓞 K)) (hG : G ≠ 0) (hV : V ≠ 0) :
    (Ideal.absNorm G : ℝ) * (Ideal.absNorm V : ℝ) *
        Z ^ (x - idealLogLength Z G - idealLogLength Z V) = Z ^ x := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc
    _ = Z ^ (idealLogLength Z G + idealLogLength Z V) *
        Z ^ (x - idealLogLength Z G - idealLogLength Z V) := by
      rw [Real.rpow_add hz, rpow_idealLogLength Z hZ G hG,
        rpow_idealLogLength Z hZ V hV]
    _ = Z ^ x := by
      rw [← Real.rpow_add hz]
      congr 1
      ring

/-- A genuine divisor of the old mask and the two frequency radicals
inherits the required support exponent. No squarefreeness approximation
or equal-prime-norm approximation enters this estimate. -/
theorem moving_support_window_of_dvd
    (Z : ℝ) (hZ : 1 < Z) (q : ℝ)
    (moving old unit nonunit : A.Exterior)
    (hdiv : moving.val ∣ old.val * unit.val * nonunit.val)
    (hold : A.exteriorNorm old ≤ Z ^ q) :
    A.exteriorNorm moving ≤ Z ^
      (q + idealLogLength Z unit.val + idealLogLength Z nonunit.val) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hn : A.exteriorNorm moving ≤
      A.exteriorNorm old * A.exteriorNorm unit * A.exteriorNorm nonunit := by
    change (Ideal.absNorm moving.val : ℝ) ≤
      (Ideal.absNorm old.val : ℝ) * (Ideal.absNorm unit.val : ℝ) *
        (Ideal.absNorm nonunit.val : ℝ)
    simpa only [map_mul, Nat.cast_mul] using
      (norm_le_of_dvd
        (mul_ne_zero (mul_ne_zero old.property.1 unit.property.1) nonunit.property.1) hdiv)
  calc
    A.exteriorNorm moving ≤
        A.exteriorNorm old * A.exteriorNorm unit * A.exteriorNorm nonunit := hn
    _ ≤ (Z ^ q * A.exteriorNorm unit) * A.exteriorNorm nonunit :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hold (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = Z ^ (q + idealLogLength Z unit.val + idealLogLength Z nonunit.val) := by
      rw [Real.rpow_add hz, Real.rpow_add hz,
        rpow_idealLogLength Z hZ unit.val unit.property.1,
        rpow_idealLogLength Z hZ nonunit.val nonunit.property.1]
      rfl

namespace ActualSecondCorrelationRows

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)

/-- The new row exponent follows from the original frequency norm
window and the literal extraction factor of the complete correlation. -/
theorem original_window_after_extraction
    (Z : ℝ) (hZ : 1 < Z) (x : ℝ) (h : R.live)
    (hrow : A.exteriorNorm (R.originalIdeal h.val) ≤ Z ^ x) :
    A.exteriorNorm (R.originalIdeal h.val) ≤
      R.normFactor C h.val *
        Z ^ (x -
          idealLogLength Z (gcd (primePowerProduct R.primes R.leftMultiplicity).val
            (primePowerProduct R.primes R.rightMultiplicity).val) -
          idealLogLength Z
            (nonunitFrequencyRadical C R.primes R.leftMultiplicity
              R.rightMultiplicity (R.frequency h.val)).val) := by
  apply hrow.trans_eq
  symm
  exact extraction_norm_rpow_window Z hZ x _ _
    (gcd_ne_zero_of_left (primePowerProduct R.primes R.leftMultiplicity).property.1)
    (nonunitFrequencyRadical C R.primes R.leftMultiplicity
      R.rightMultiplicity (R.frequency h.val)).property.1

/-- The literal second-transform m' and q' windows give the joint budget
on the actual extracted row. The moving mask is the one in the child's
single-ideal recipe, tied here to its actual prime factors. -/
theorem extracted_joint_window
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo krow g : ℝ) (h : R.live)
    (moving old : A.Exterior)
    (hrow : A.exteriorNorm (R.originalIdeal h.val) ≤ Z ^ (2 * a₀ - krow - g))
    (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (hdiv : moving.val ∣ old.val *
      (unitFrequencyRadical C R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h.val)).val *
      (nonunitFrequencyRadical C R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h.val)).val) :
    idealNorm K (R.extractedRow C h).momentIdeal * A.exteriorNorm moving ≤
      Z ^ secondCommonChildWidth Z a₀ q wo krow g
        (primePowerProduct R.primes R.leftMultiplicity).val
        (primePowerProduct R.primes R.rightMultiplicity).val
        (unitFrequencyRadical C R.primes R.leftMultiplicity
          R.rightMultiplicity (R.frequency h.val)).val
        (nonunitFrequencyRadical C R.primes R.leftMultiplicity
          R.rightMultiplicity (R.frequency h.val)).val := by
  exact (R.extractedRow C h).joint_norm_le_of_windows moving Z _ _
    (zero_lt_one.trans hZ)
    (R.original_window_after_extraction C Z hZ (2 * a₀ - krow - g) h hrow)
    (moving_support_window_of_dvd Z hZ (q + wo) moving old _ _ hdiv hold)

end ActualSecondCorrelationRows

namespace ActualHybridLeaf.NormalizationData

variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {leaf : ActualHybridLeaf K H U E}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- Separate original windows for the two actual sides of each of the
four rectangles. The final joint budget is not an input field. -/
structure JointWindowInput where
  leftMask : ∀ r, ActualMovingMaskRecipe A (N.left r).calibration.data
  rightMask : ∀ r, ActualMovingMaskRecipe A (N.right r).calibration.data
  leftWindows : ∀ r, (N.left r).calibration.RowWindows (leftMask r)
  rightWindows : ∀ r, (N.right r).calibration.RowWindows (rightMask r)

/-- This fills the source fields required by the filtered-child producer
using only the separate original row and mask windows. -/
def JointWindowInput.toJointRowInput (W : N.JointWindowInput) : N.JointRowInput where
  leftMask := W.leftMask
  rightMask := W.rightMask
  left_budget r := (W.leftWindows r).source_budget
  right_budget r := (W.rightWindows r).source_budget

end ActualHybridLeaf.NormalizationData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.joint_row_product_of_separate_windows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.extracted_joint_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.JointWindowInput.toJointRowInput

