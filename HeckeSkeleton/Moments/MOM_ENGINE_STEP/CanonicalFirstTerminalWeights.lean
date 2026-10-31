import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOrdinaryWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstTerminalIndexMass

/-!
# The two original second terminals keep their first divisor

A second zero or tail has no second-common or second-divisor label.
The identities here therefore expose only the original first common
ideals, first divisor, finite phase, two literal first Cauchy allowances,
and the mass of the original first Fourier kernel. Both direct and
amplified sources use this same first coefficient. No second-label
carrier or additional norm payment is inserted.

The original first profile window gives the exact firstCommonWeight
used by FirstTerminalIndexMass. The inverse first-divisor norm is left
to the original active-column frozen-atom calculation.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

/-- Preserve the first common weight itself until the first-only
terminal carrier is summed. This uses just the original profile window. -/
theorem firstOriginalAllowanceWeight_le_common
    (Z parentWidth total rawProfile profileCost : ℝ) (hZ : 1 < Z)
    (hprofile : rawProfile ≤ profileCost * Z ^ (parentWidth - total))
    (D E : Ideal (𝓞 K)) :
    firstOriginalAllowanceWeight Z parentWidth total rawProfile D E ≤
      profileCost * firstCommonWeight Z D E := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc
    _ ≤ (profileCost * Z ^ (parentWidth - total)) *
        Real.sqrt (Ideal.absNorm (firstActiveRadical D E) : ℝ) *
        Real.sqrt (firstLeftAllowance Z total D E) *
        Real.sqrt (firstRightAllowance Z total D E) / Z ^ parentWidth := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hprofile (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← first_allowance_scalar_identity Z total parentWidth hZ D E]
      ring

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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

namespace FirstBlockPoolData.SecondStages.TerminalCalibration

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)

/-- The original zero class after parent normalization has one first
Fourier measure and the two actual first allowances. -/
theorem classZeroBudget_relative
    (ε Czero parentWidth total : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    T.classZeroBudget NL NR ε Czero S χ / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        (actualFourierMeasure chart.kernel).real Set.univ *
        ((T.left S χ).zeroBudget ε Czero / firstLeftAllowance Z total DE.1 DE.2 +
          (T.right S χ).zeroBudget ε Czero / firstRightAllowance Z total DE.1 DE.2) := by
  simp only [classZeroBudget, FirstBlockPoolData.SecondStages.classWeight, FirstBlockPoolData.rowBound,
    hleftScale, hrightScale, b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

/-- The original tail class after parent normalization has one first
Fourier measure and the two actual first allowances. -/
theorem classTailBudget_relative
    (Cerror parentWidth total : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    T.classTailBudget NL NR Cerror S χ / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        (actualFourierMeasure chart.kernel).real Set.univ *
        ((T.left S χ).tailBudget Cerror / firstLeftAllowance Z total DE.1 DE.2 +
          (T.right S χ).tailBudget Cerror / firstRightAllowance Z total DE.1 DE.2) := by
  simp only [classTailBudget, FirstBlockPoolData.SecondStages.classWeight, FirstBlockPoolData.rowBound,
    hleftScale, hrightScale, b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

end FirstBlockPoolData.SecondStages.TerminalCalibration

namespace FirstBlockDirectData.SecondStages.TerminalCalibration

variable {p : FirstBlockDirectData chart M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)

/-- The original zero class after parent normalization has one first
Fourier measure and the two actual first allowances. -/
theorem classZeroBudget_relative
    (ε Czero parentWidth total : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    T.classZeroBudget NL NR ε Czero S χ / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        (actualFourierMeasure chart.kernel).real Set.univ *
        ((T.left S χ).zeroBudget ε Czero / firstLeftAllowance Z total DE.1 DE.2 +
          (T.right S χ).zeroBudget ε Czero / firstRightAllowance Z total DE.1 DE.2) := by
  simp only [classZeroBudget, FirstBlockDirectData.SecondStages.classWeight, FirstBlockDirectData.rowBound,
    hleftScale, hrightScale, b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

/-- The original tail class after parent normalization has one first
Fourier measure and the two actual first allowances. -/
theorem classTailBudget_relative
    (Cerror parentWidth total : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (hleftScale : NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : NR S χ = firstRightAllowance Z total DE.1 DE.2) :
    T.classTailBudget NL NR Cerror S χ / Z ^ parentWidth =
      ‖(moebius S.val : ℂ)‖ * ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 / 2) *
        (actualFourierMeasure chart.kernel).real Set.univ *
        ((T.left S χ).tailBudget Cerror / firstLeftAllowance Z total DE.1 DE.2 +
          (T.right S χ).tailBudget Cerror / firstRightAllowance Z total DE.1 DE.2) := by
  simp only [classTailBudget, FirstBlockDirectData.SecondStages.classWeight, FirstBlockDirectData.rowBound,
    hleftScale, hrightScale, b.activeNorm_eq, firstOriginalAllowanceWeight]
  ring

end FirstBlockDirectData.SecondStages.TerminalCalibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstOriginalAllowanceWeight_le_common
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.TerminalCalibration.classZeroBudget_relative
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.TerminalCalibration.classTailBudget_relative

