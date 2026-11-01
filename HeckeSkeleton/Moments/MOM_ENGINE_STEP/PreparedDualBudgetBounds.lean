import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualSupportedStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectCoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSourceFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalPower

/-!
# Original terminal budgets after the justified source preparation

Support preparation sets the physical fibre of an empty source to zero.
The additional coefficient gate keeps that fibre and every terminal
window unchanged. Thus both nonnegative terminal budgets decrease.
The same comparison is summed through the original pool tags, divisor
classes and parent labels, retaining their original positive weights.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

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
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

local instance preparedDualBudgetBoundsCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.DualTerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)

@[simp] theorem gated_zeroBudget (ε Czero : ℝ) :
    T.gated.zeroBudget ε Czero = T.zeroBudget ε Czero := rfl

@[simp] theorem gated_tailBudget (Cerror : ℝ) :
    T.gated.tailBudget Cerror = T.tailBudget Cerror := rfl

theorem supported_zeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    T.supported.zeroBudget ε Czero ≤ T.zeroBudget ε Czero := by
  by_cases hrows : G.rows = ∅
  · simpa only [zeroBudget, supported, ActualGaussStage.supported,
      if_pos hrows, Nat.cast_zero, zero_mul] using T.zeroBudget_nonneg ε Czero hC
  · simp only [zeroBudget, supported, ActualGaussStage.supported, if_neg hrows]

theorem supported_tailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    T.supported.tailBudget Cerror ≤ T.tailBudget Cerror := by
  by_cases hrows : G.rows = ∅
  · simpa only [tailBudget, supported, ActualGaussStage.supported,
      if_pos hrows, Nat.cast_zero, zero_mul] using T.tailBudget_nonneg Cerror hC
  · simp only [tailBudget, supported, ActualGaussStage.supported, if_neg hrows]

theorem supported_gated_zeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    T.supported.gated.zeroBudget ε Czero ≤ T.zeroBudget ε Czero := by
  simpa only [gated_zeroBudget] using T.supported_zeroBudget_le ε Czero hC

theorem supported_gated_tailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    T.supported.gated.tailBudget Cerror ≤ T.tailBudget Cerror := by
  simpa only [gated_tailBudget] using T.supported_tailBudget_le Cerror hC

end ActualGaussStage.DualTerminalCalibration

section Pool

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace ActualPoolStages.DualTerminalCalibration

variable {ι : Type*} {dpool : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest}
variable (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)

theorem supported_gated_zeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    T.supported.gated.zeroBudget ε Czero ≤ T.zeroBudget ε Czero := by
  unfold zeroBudget
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) dpool.density_pos.le)
  apply Finset.sum_le_sum
  intro tag _
  apply mul_le_mul_of_nonneg_left _ (dpool.tagWeight_nonneg tag)
  rcases tag with u | p | p | p
  · exact T.main.supported_gated_zeroBudget_le ε Czero hC
  · exact (T.one p).supported_gated_zeroBudget_le ε Czero hC
  · exact (T.six p).supported_gated_zeroBudget_le ε Czero hC
  · exact (T.seven p).supported_gated_zeroBudget_le ε Czero hC

theorem supported_gated_tailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    T.supported.gated.tailBudget Cerror ≤ T.tailBudget Cerror := by
  unfold tailBudget
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) dpool.density_pos.le)
  apply Finset.sum_le_sum
  intro tag _
  apply mul_le_mul_of_nonneg_left _ (dpool.tagWeight_nonneg tag)
  rcases tag with u | p | p | p
  · exact T.main.supported_gated_tailBudget_le Cerror hC
  · exact (T.one p).supported_gated_tailBudget_le Cerror hC
  · exact (T.six p).supported_gated_tailBudget_le Cerror hC
  · exact (T.seven p).supported_gated_tailBudget_le Cerror hC

end ActualPoolStages.DualTerminalCalibration

namespace FirstBlockPoolData.SecondStages.DualTerminalCalibration

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
variable (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
  ((PUnit × PUnit) →* Circle) → ℝ)
variable (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

include hNL hNR

theorem supported_gated_zeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    T.supported.gated.zeroBudget NL NR ε Czero ≤ T.zeroBudget NL NR ε Czero := by
  unfold zeroBudget
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  unfold classZeroBudget
  apply mul_le_mul_of_nonneg_left _ (classWeight_nonneg NL NR S χ)
  exact add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.left S χ).supported_gated_zeroBudget_le ε Czero hC)
        ENNReal.toReal_nonneg) (hNL S χ).le)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.right S χ).supported_gated_zeroBudget_le ε Czero hC)
        ENNReal.toReal_nonneg) (hNR S χ).le)

theorem supported_gated_tailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    T.supported.gated.tailBudget NL NR Cerror ≤ T.tailBudget NL NR Cerror := by
  unfold tailBudget
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  unfold classTailBudget
  apply mul_le_mul_of_nonneg_left _ (classWeight_nonneg NL NR S χ)
  exact add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.left S χ).supported_gated_tailBudget_le Cerror hC)
        ENNReal.toReal_nonneg) (hNL S χ).le)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.right S χ).supported_gated_tailBudget_le Cerror hC)
        ENNReal.toReal_nonneg) (hNR S χ).le)

end FirstBlockPoolData.SecondStages.DualTerminalCalibration

namespace ActualFirstSource.SecondStages.DualTerminalCalibration

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}
variable (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
variable (N : s.Normalization)

theorem supported_gated_dualSecondZeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    R.supported.gated.dualSecondZeroBudget T.supported.gated N ε Czero ≤
      R.dualSecondZeroBudget T N ε Czero := by
  unfold ActualFirstSource.SecondStages.dualSecondZeroBudget
    ActualFirstSource.SecondStages.dualZeroBudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).supported_gated_zeroBudget_le
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Czero hC

theorem supported_gated_dualSecondTailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    R.supported.gated.dualSecondTailBudget T.supported.gated N Cerror ≤
      R.dualSecondTailBudget T N Cerror := by
  unfold ActualFirstSource.SecondStages.dualSecondTailBudget
    ActualFirstSource.SecondStages.dualTailBudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).supported_gated_tailBudget_le
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) Cerror hC

end ActualFirstSource.SecondStages.DualTerminalCalibration

end Pool

namespace FirstBlockDirectData.SecondStages.DualTerminalCalibration

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
variable (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
  ((PUnit × PUnit) →* Circle) → ℝ)
variable (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

include hNL hNR

theorem prepared_zeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    T.prepared.zeroBudget NL NR ε Czero ≤ T.zeroBudget NL NR ε Czero := by
  unfold zeroBudget
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  unfold classZeroBudget
  apply mul_le_mul_of_nonneg_left _ (classWeight_nonneg NL NR S χ)
  exact add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.left S χ).supported_gated_zeroBudget_le ε Czero hC)
        ENNReal.toReal_nonneg) (hNL S χ).le)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.right S χ).supported_gated_zeroBudget_le ε Czero hC)
        ENNReal.toReal_nonneg) (hNR S χ).le)

theorem prepared_tailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    T.prepared.tailBudget NL NR Cerror ≤ T.tailBudget NL NR Cerror := by
  unfold tailBudget
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  unfold classTailBudget
  apply mul_le_mul_of_nonneg_left _ (classWeight_nonneg NL NR S χ)
  exact add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.left S χ).supported_gated_tailBudget_le Cerror hC)
        ENNReal.toReal_nonneg) (hNL S χ).le)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((T.right S χ).supported_gated_tailBudget_le Cerror hC)
        ENNReal.toReal_nonneg) (hNR S χ).le)

end FirstBlockDirectData.SecondStages.DualTerminalCalibration

namespace ActualDirectFirstSource.SecondStages.DualTerminalCalibration

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}
variable (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
variable (N : s.Normalization)

theorem prepared_dualSecondZeroBudget_le (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    R.prepared.dualSecondZeroBudget T.prepared N ε Czero ≤
      R.dualSecondZeroBudget T N ε Czero := by
  unfold ActualDirectFirstSource.SecondStages.dualSecondZeroBudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).prepared_zeroBudget_le
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Czero hC

theorem prepared_dualSecondTailBudget_le (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    R.prepared.dualSecondTailBudget T.prepared N Cerror ≤
      R.dualSecondTailBudget T N Cerror := by
  unfold ActualDirectFirstSource.SecondStages.dualSecondTailBudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).prepared_tailBudget_le
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) Cerror hC

end ActualDirectFirstSource.SecondStages.DualTerminalCalibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.supported_gated_zeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.supported_gated_tailBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.supported_gated_zeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.DualTerminalCalibration.supported_gated_dualSecondZeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.DualTerminalCalibration.supported_gated_dualSecondTailBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.DualTerminalCalibration.prepared_dualSecondZeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.DualTerminalCalibration.prepared_dualSecondTailBudget_le
