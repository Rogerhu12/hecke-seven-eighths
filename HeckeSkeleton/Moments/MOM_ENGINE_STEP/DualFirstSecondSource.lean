import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondRawSource

/-!
# The original parent through both signed transforms

The same first common-support, mask-divisor, original residual-divisor,
finite phase and prime-pool labels are retained. Each second stage is
attached to its original source. Its signed-origin conditions concern
only its individual tensor and additional mask, and its terminal data
contain only the original profile and factor windows.

The complete first and second reductions are proved internally. Both
pure-dual zeros and both original cutoff tails are paid before the
literal finite nonzero second rows are used by the hybrid partition.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

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
variable {W E : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance dualFirstSecondSourceCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

namespace SecondStages

variable {p : FirstBlockPoolData chart P M X hX}

structure DualSourceConditions (s : p.SecondStages (E := E) (hDiff := hDiff)) : Prop where
  left : ∀ S χ, (s.left S χ).DualSourceConditions
  right : ∀ S χ, (s.right S χ).DualSourceConditions

structure DualTerminalCalibration (s : p.SecondStages (E := E) (hDiff := hDiff))
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  left : ∀ S χ, (s.left S χ).DualTerminalCalibration sTail sZero k Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).DualTerminalCalibration sTail sZero k Lmax Nsave decay

namespace DualTerminalCalibration

variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def rawCost (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (PUnit × PUnit) →* Circle, ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, (T.left S χ).rawPhaseCost chart.leftPoint ξ ε Cerror Czero / NL S χ
          ∂actualFourierMeasure chart.kernel) +
        ∫ ξ, (T.right S χ).rawPhaseCost (fun j => -chart.rightPoint j) ξ ε Cerror Czero / NR S χ
          ∂actualFourierMeasure chart.kernel)

/-- This substitution lemma is used with the engine's proved universal
pool-stage theorem. The final parent theorem constructs that theorem;
it is not an extra source calibration field. -/
theorem linearized_le_rawCost
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (conditions : s.DualSourceConditions)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ)
    (hstage : ∀ {j : Type*} (d : FirstGaussPoolData C P j) (c : j → ℂ) (x : j → W)
      (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
      (hs : s.DualSourceConditions)
      (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) (ξ : W),
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.rawPhaseCost x ξ ε Cerror Czero) :
    p.linearizedCost NL NR ≤ T.rawCost NL NR ε Cerror Czero := by
  unfold FirstBlockPoolData.linearizedCost firstDivisorLinearizedCost rawCost
  apply Finset.sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ hχ
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (norm_nonneg _) (div_nonneg
      (mul_nonneg (mul_nonneg p.rowBound_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (by norm_num)))
  apply add_le_add
  · apply integral_mono
      ((p.divisorPools.leftData S).normalized_twisted_integrable chart.kernel
        (p.leftDivisorCoefficient S χ) chart.leftPoint (NL S χ))
      (((T.left S χ).rawPhaseCost_integrable chart.kernel chart.leftPoint ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      (hstage _ _ chart.leftPoint (s.left S χ) (conditions.left S χ) (T.left S χ) ξ) (hNL S χ).le
  · apply integral_mono
      ((p.divisorPools.rightData S).normalized_twisted_integrable chart.kernel
        (p.rightDivisorCoefficient S χ) (fun j => -chart.rightPoint j) (NR S χ))
      (((T.right S χ).rawPhaseCost_integrable chart.kernel
        (fun j => -chart.rightPoint j) ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      (hstage _ _ (fun j => -chart.rightPoint j) (s.right S χ) (conditions.right S χ) (T.right S χ) ξ) (hNR S χ).le

end DualTerminalCalibration
end SecondStages
end FirstBlockPoolData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))

abbrev DualSourceConditions : Prop :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).DualSourceConditions

abbrev DualTerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).DualTerminalCalibration sTail sZero k Lmax Nsave decay
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def dualRawCost (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).rawCost (N.left v D) (N.right v D) ε Cerror Czero

end ActualFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
include ν μ in
/-- The complete original parent reaches the raw second rows, with
both true dual zeros and both physical tails bounded internally. -/
theorem actual_parent_two_stage_dual_raw_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (rowBallSize : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ coefficient : s.Column → ℂ,
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ conditions : R.DualSourceConditions,
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero + R.dualRawCost T N ε Cerror Czero) := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero,
      CfirstError, CfirstZero, hCfE, hCfZ, hparent⟩ :=
    actual_parent_first_dual_terminal_bound (E := W) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff rowBallSize k ε hε Lmax Nsave ξmax hξmax
  obtain ⟨decayPool, hdecayPool, hchoicePool, hqPool, sTail, sZero,
      Cerror, Czero, hCE, hCZ, hpool⟩ :=
    actual_pool_dual_raw_fourier_stage_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD (rowBallFiniteFamily K A.Sf rowBallSize)
      (rowBallFiniteFamily_locallyConstant K A.Sf rowBallSize)
      (rowBallFiniteFamily_compactSupport K A.Sf rowBallSize)
      k ε hε Lmax Nsave ξmax hξmax
  have hdecay_eq : decayPool = decay := hchoicePool.trans hchoice.symm
  rw [hdecay_eq] at hpool
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles
    N R conditions T F
  obtain ⟨hcutoff, _, hlinear⟩ :=
    hparent Z ell eps bad P centered d a t Y₁ Y₂ X hX s coefficient hprofiles F
  refine ⟨hcutoff, (hlinear N).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  apply add_le_add le_rfl
  unfold ActualFirstSource.linearizedCost ActualFirstSource.SecondStages.dualRawCost
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).linearized_le_rawCost (conditions v D)
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero
    (fun {j} d c x s hs T ξ => hpool Z ell eps bad P d c x s hs T ξ)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualTerminalCalibration.linearized_le_rawCost
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_dual_raw_terminal_bound
