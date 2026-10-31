import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectCoveredStage

/-!
# Pure-dual direct terminals from the same original atoms

The original direct coefficient atoms, support-extraction multiplicity,
first-divisor denominator and first Fourier control are reused. Only
the residual profile record changes to the pure-dual calibration, so
its actual nonzero value at the origin is retained.

Both source sides remain at their original divisor and phase label.
The side powers are divided by their literal original first allowances
before the common scalar is applied. No prime pool, aggregate energy,
or terminal estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance dualDirectSecondTerminalAtomsCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {mask : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart mask X hX}
variable {Z : ℝ}

namespace SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))

/-- Original frozen atoms and residual windows for every actual shared
first divisor and finite phase.  The columns themselves are unchanged. -/
structure DualFirstDivisorWindows (slotsL slotsR : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  leftAtoms : ∀ S χ, FirstDivisorCoefficientAtoms (A := A) (σ := σ)
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).columns
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).coefficient S.val slotsL B
  rightAtoms : ∀ S χ, FirstDivisorCoefficientAtoms (A := A) (σ := σ)
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).columns
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).coefficient S.val slotsR B
  left : ∀ S χ, (s.left S χ).DualResidualTerminalWindows (leftAtoms S χ)
    sTail sZero k Z Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).DualResidualTerminalWindows (rightAtoms S χ)
    sTail sZero k Z Lmax Nsave decay

namespace DualFirstDivisorWindows

variable {s} {slotsL slotsR k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}
variable (T : s.DualFirstDivisorWindows slotsL slotsR B sTail sZero k Z Lmax Nsave decay)

def calibration : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  left S χ := (T.left S χ).calibration
  right S χ := (T.right S χ).calibration

structure ZeroWindows
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (ε total loss profileL profileR : ℝ) (fiberCap maskCap : ℕ) : Prop where
  left_tuples : (T.left S χ).windows.multiplicity = idealDivisorCount (DE.1 ^ 2) ^ k
  right_tuples : (T.right S χ).windows.multiplicity = idealDivisorCount (DE.2 ^ 2) ^ k
  left_fiber : (s.left S χ).fiber ≤ fiberCap
  right_fiber : (s.right S χ).fiber ≤ fiberCap
  left_mask : (s.left S χ).mask.card ≤ maskCap
  right_mask : (s.right S χ).mask.card ≤ maskCap
  left_profile : (T.left S χ).zeroProfileConstant ≤ profileL
  right_profile : (T.right S χ).zeroProfileConstant ≤ profileR
  left_ledger : (T.left S χ).zeroExponent + (T.left S χ).productExponent * ε ≤
    (total - idealLogLength Z DE.1 +
      firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss
  right_ledger : (T.right S χ).zeroExponent + (T.right S χ).productExponent * ε ≤
    (total - idealLogLength Z DE.2 +
      firstAllowance (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss

/-- Actual direct zero class, including its original first Fourier
mass and both first allowances, derived from original profile atoms. -/
theorem classZeroBudget_le_original_profiles (hZ : 1 < Z)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (ε Czero total parentWidth loss firstAmplitude profileL profileR : ℝ)
    (fiberCap maskCap : ℕ)
    (U : T.ZeroWindows S χ ε total loss profileL profileR fiberCap maskCap)
    (hC : 0 ≤ Czero) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total)) :
    T.calibration.classZeroBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) ε Czero S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((directFirstDivisorZeroCoefficient B Czero profileL slotsL k fiberCap maskCap DE.1 +
          directFirstDivisorZeroCoefficient B Czero profileR slotsR k fiberCap maskCap DE.2) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 * (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hB : 0 ≤ B := zero_le_one.trans (T.leftAtoms S χ).bound_ge_one
  have hCL : 0 ≤ directFirstDivisorZeroCoefficient B Czero profileL
      slotsL k fiberCap maskCap DE.1 := by unfold directFirstDivisorZeroCoefficient; positivity
  have hCR : 0 ≤ directFirstDivisorZeroCoefficient B Czero profileR
      slotsR k fiberCap maskCap DE.2 := by unfold directFirstDivisorZeroCoefficient; positivity
  have hL := (T.left S χ).direct_zeroBudget_div_allowance_le DE.1 U.left_tuples
    ε Czero profileL _ loss fiberCap maskCap hC hprofileL U.left_fiber U.left_mask
    U.left_profile U.left_ledger
  have hR := (T.right S χ).direct_zeroBudget_div_allowance_le DE.2 U.right_tuples
    ε Czero profileR _ loss fiberCap maskCap hC hprofileR U.right_fiber U.right_mask
    U.right_profile U.right_ledger
  have hc := original_terminal_class_scalar Z parentWidth
    (firstLeftAllowance Z total DE.1 DE.2) (firstRightAllowance Z total DE.1 DE.2)
    p.rowBound ‖(moebius S.val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖
    ((actualFourierMeasure chart.kernel).real Set.univ) (firstTerminalFourierCost chart.kernel)
    ((T.left S χ).calibration.zeroBudget ε Czero) ((T.right S χ).calibration.zeroBudget ε Czero)
    _ _ (Ideal.absNorm S.val : ℝ) loss firstAmplitude (firstCommonWeight Z DE.1 DE.2)
    hz (firstLeftAllowance_pos Z total hz _ _) (firstRightAllowance_pos Z total hz _ _)
    p.rowBound_nonneg (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (firstTerminalFourierCost_nonneg chart.kernel) hCL hCR (Nat.cast_nonneg _) hL hR
    (firstTerminalFourierCost_bound chart.kernel)
    (p.normalized_allowance_prefactor hZ total parentWidth firstAmplitude hfirst)
  simpa only [calibration, DualTerminalCalibration.classZeroBudget, classWeight] using hc

structure TailWindows
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (total loss profileL profileR exponentL exponentR : ℝ) (fiberCap : ℕ) : Prop where
  left_tuples : (T.left S χ).windows.multiplicity = idealDivisorCount (DE.1 ^ 2) ^ k
  right_tuples : (T.right S χ).windows.multiplicity = idealDivisorCount (DE.2 ^ 2) ^ k
  left_fiber : (s.left S χ).fiber ≤ fiberCap
  right_fiber : (s.right S χ).fiber ≤ fiberCap
  left_profile : (T.left S χ).tailProfileConstant ≤ profileL * Z ^ exponentL
  right_profile : (T.right S χ).tailProfileConstant ≤ profileR * Z ^ exponentR
  left_ledger : exponentL - Nsave ≤
    (total - idealLogLength Z DE.1 +
      firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss
  right_ledger : exponentR - Nsave ≤
    (total - idealLogLength Z DE.2 +
      firstAllowance (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss

theorem classTailBudget_le_original_profiles (hZ : 1 < Z)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (Cerror total parentWidth loss firstAmplitude profileL profileR exponentL exponentR : ℝ)
    (fiberCap : ℕ)
    (U : T.TailWindows S χ total loss profileL profileR exponentL exponentR fiberCap)
    (hC : 0 ≤ Cerror) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total)) :
    T.calibration.classTailBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) Cerror S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((directFirstDivisorTailCoefficient B Cerror profileL slotsL k fiberCap DE.1 +
          directFirstDivisorTailCoefficient B Cerror profileR slotsR k fiberCap DE.2) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 * (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hB : 0 ≤ B := zero_le_one.trans (T.leftAtoms S χ).bound_ge_one
  have hCL : 0 ≤ directFirstDivisorTailCoefficient B Cerror profileL
      slotsL k fiberCap DE.1 := by unfold directFirstDivisorTailCoefficient; positivity
  have hCR : 0 ≤ directFirstDivisorTailCoefficient B Cerror profileR
      slotsR k fiberCap DE.2 := by unfold directFirstDivisorTailCoefficient; positivity
  have hL := (T.left S χ).direct_tailBudget_div_allowance_le DE.1 U.left_tuples
    Cerror profileL exponentL _ loss fiberCap hC hprofileL U.left_fiber U.left_profile U.left_ledger
  have hR := (T.right S χ).direct_tailBudget_div_allowance_le DE.2 U.right_tuples
    Cerror profileR exponentR _ loss fiberCap hC hprofileR U.right_fiber U.right_profile U.right_ledger
  have hc := original_terminal_class_scalar Z parentWidth
    (firstLeftAllowance Z total DE.1 DE.2) (firstRightAllowance Z total DE.1 DE.2)
    p.rowBound ‖(moebius S.val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖
    ((actualFourierMeasure chart.kernel).real Set.univ) (firstTerminalFourierCost chart.kernel)
    ((T.left S χ).calibration.tailBudget Cerror) ((T.right S χ).calibration.tailBudget Cerror)
    _ _ (Ideal.absNorm S.val : ℝ) loss firstAmplitude (firstCommonWeight Z DE.1 DE.2)
    hz (firstLeftAllowance_pos Z total hz _ _) (firstRightAllowance_pos Z total hz _ _)
    p.rowBound_nonneg (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (firstTerminalFourierCost_nonneg chart.kernel) hCL hCR (Nat.cast_nonneg _) hL hR
    (firstTerminalFourierCost_bound chart.kernel)
    (p.normalized_allowance_prefactor hZ total parentWidth firstAmplitude hfirst)
  simpa only [calibration, DualTerminalCalibration.classTailBudget, classWeight] using hc

end DualFirstDivisorWindows
end SecondStages
end FirstBlockDirectData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.DualFirstDivisorWindows.classZeroBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.DualFirstDivisorWindows.classTailBudget_le_original_profiles
