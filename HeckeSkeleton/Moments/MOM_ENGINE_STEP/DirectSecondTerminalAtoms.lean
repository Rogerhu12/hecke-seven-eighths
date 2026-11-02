import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorBlockTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstTerminalWeights

set_option linter.unusedSectionVars false

/-!
# Direct second terminals from their original coefficient atoms

The unamplified entrance uses the same residual-profile calibration and
the same first Cauchy allowances as the amplified entrance.  Its genuine
support-extraction tuple multiplicity is `τ(D²)^k`.  No prime-pool
density, amplifier valuation, or pool scalar occurs in this calculation.

Every first-divisor denominator is proved by the original frozen atoms.
The source columns, their divisibility gates, the first finite character,
and the original first Fourier kernel are retained literally.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

def directFirstDivisorZeroCoefficient (B Czero profileConstant : ℝ)
    (slots k fiberCap maskCap : ℕ) (D : Ideal (𝓞 K)) : ℝ :=
  (fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k : ℕ) * Czero *
    (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap)

def directFirstDivisorTailCoefficient (B Cerror profileConstant : ℝ)
    (slots k fiberCap : ℕ) (D : Ideal (𝓞 K)) : ℝ :=
  (fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k : ℕ) * Cerror *
    (B ^ slots * profileConstant)

private theorem direct_allowance_power_cancel
    (Z allowance loss coefficient : ℝ) (hZ : 0 < Z) :
    (coefficient * Z ^ (allowance + loss)) / Z ^ allowance =
      coefficient * Z ^ loss := by
  sorry

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

namespace ActualGaussStage.ResidualTerminalWindows

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {S : Ideal (𝓞 K)} {slots k : ℕ} {B Z Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}
variable {atoms : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
  G.columns G.coefficient S slots B}
variable (T : s.ResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay)

def zeroExponent : ℝ :=
  T.zeroProfileExponent + T.zeroColumnExponent +
    T.inverseRadiusExponent + T.productExponent / 2

/-- The direct zero budget is calibrated from individual original
residual profiles and exact support-tuple metadata. -/
theorem direct_zeroBudget_div_allowance_le
    (D : Ideal (𝓞 K))
    (hmult : T.windows.multiplicity = idealDivisorCount (D ^ 2) ^ k)
    (ε Czero profileConstant allowance loss : ℝ) (fiberCap maskCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hfiber : s.fiber ≤ fiberCap) (hmask : s.mask.card ≤ maskCap)
    (hraw : T.zeroProfileConstant ≤ profileConstant)
    (hbudget : T.zeroExponent + T.productExponent * ε ≤ allowance + loss) :
    T.calibration.zeroBudget ε Czero / Z ^ allowance ≤
      (directFirstDivisorZeroCoefficient B Czero profileConstant slots k fiberCap maskCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ loss := by
  sorry

/-- The direct tail uses the same original coefficient atoms and
support fibres; only its primitive residual-profile decay ledger differs. -/
theorem direct_tailBudget_div_allowance_le
    (D : Ideal (𝓞 K))
    (hmult : T.windows.multiplicity = idealDivisorCount (D ^ 2) ^ k)
    (Cerror profileConstant profileExponent allowance loss : ℝ) (fiberCap : ℕ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hfiber : s.fiber ≤ fiberCap)
    (hraw : T.tailProfileConstant ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent - Nsave ≤ allowance + loss) :
    T.calibration.tailBudget Cerror / Z ^ allowance ≤
      (directFirstDivisorTailCoefficient B Cerror profileConstant slots k fiberCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ loss := by
  sorry

end ActualGaussStage.ResidualTerminalWindows

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance directSecondTerminalAtomsCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

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

/-- The literal two first allowances give the same common-support
weight on a direct source, without any pool data. -/
theorem normalized_allowance_prefactor (p : FirstBlockDirectData chart mask X hX)
    (hZ : 1 < Z) (total parentWidth amplitude : ℝ)
    (hprofile : p.weightBound ≤ amplitude * Z ^ (parentWidth - total)) :
    p.rowBound * Real.sqrt (firstLeftAllowance Z total DE.1 DE.2) *
        Real.sqrt (firstRightAllowance Z total DE.1 DE.2) / Z ^ parentWidth ≤
      amplitude * firstCommonWeight Z DE.1 DE.2 := by
  sorry

namespace SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))

/-- Original frozen atoms and residual windows for every actual shared
first divisor and finite phase.  The columns themselves are unchanged. -/
structure FirstDivisorWindows (slotsL slotsR : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  leftAtoms : ∀ S χ, FirstDivisorCoefficientAtoms (A := A) (σ := σ)
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).columns
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).coefficient S.val slotsL B
  rightAtoms : ∀ S χ, FirstDivisorCoefficientAtoms (A := A) (σ := σ)
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).columns
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).coefficient S.val slotsR B
  left : ∀ S χ, (s.left S χ).ResidualTerminalWindows (leftAtoms S χ)
    sTail sZero k Z Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).ResidualTerminalWindows (rightAtoms S χ)
    sTail sZero k Z Lmax Nsave decay

namespace FirstDivisorWindows

variable {s} {slotsL slotsR k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}
variable (T : s.FirstDivisorWindows slotsL slotsR B sTail sZero k Z Lmax Nsave decay)

def calibration : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay where
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
  sorry

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
  sorry

end FirstDivisorWindows
end SecondStages
end FirstBlockDirectData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.ResidualTerminalWindows.direct_zeroBudget_div_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.ResidualTerminalWindows.direct_tailBudget_div_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.FirstDivisorWindows.classZeroBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.FirstDivisorWindows.classTailBudget_le_original_profiles
