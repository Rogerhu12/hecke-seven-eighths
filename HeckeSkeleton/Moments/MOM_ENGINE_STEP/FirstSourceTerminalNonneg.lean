import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSourceFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalTerminalBudget

set_option linter.unusedSectionVars false

/-!
# Nonnegativity of the four literal terminal budgets

The two true zero terms and the truncation tails use their original
nonnegative single-profile amplitudes and exactly one pool density.
These signs follow through the actual finite source carrier; no final
terminal quantity is supplied with a new sign assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open HeckePort.Moments.MobiusRegroup

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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance firstSourceTerminalNonnegCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

namespace ActualGaussStage.TerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest} {Z : ℝ}
variable (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)

theorem zeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ T.zeroBudget ε Czero := by
  sorry

theorem tailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    0 ≤ T.tailBudget Cerror := by
  sorry

end ActualGaussStage.TerminalCalibration

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}


namespace FirstBlockPoolData.SecondStages.TerminalCalibration

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
variable (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
  ((PUnit × PUnit) →* Circle) → ℝ)
variable (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

include hNL hNR

theorem zeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ T.zeroBudget NL NR ε Czero := by
  sorry

theorem tailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    0 ≤ T.tailBudget NL NR Cerror := by
  sorry

end FirstBlockPoolData.SecondStages.TerminalCalibration

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable {R : s.SecondStages (E := E) (hDiff := hDiff)}
variable (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay) (N : s.Normalization)

theorem zeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ R.zeroBudget T N ε Czero := by
  sorry

theorem tailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    0 ≤ R.tailBudget T N Cerror := by
  sorry

theorem secondZeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ R.secondZeroBudget T N ε Czero := by
  sorry

variable {sFirst sFirstZero : Finset (ℕ × ℕ)}
variable (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)

theorem firstZeroBudget_nonneg (ε CfirstZero : ℝ) (hC : 0 ≤ CfirstZero) :
    0 ≤ firstZeroBudget F ε CfirstZero := by
  sorry

theorem totalTailBudget_nonneg (CfirstError Cerror : ℝ)
    (hfirst : 0 ≤ CfirstError) (hsecond : 0 ≤ Cerror) :
    0 ≤ R.totalTailBudget T F N CfirstError Cerror := by
  sorry

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.secondZeroBudget_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.totalTailBudget_nonneg
