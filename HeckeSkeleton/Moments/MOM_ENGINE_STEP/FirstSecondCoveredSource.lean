import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondRawSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolCoverHybridStage

/-!
# The original parent reaches actual covered hybrid children

The first original Cartesian atlas determines every main and
valuation-error cover, also after the internal common Moebius divisor
is frozen.  All physical row carriers, exact one-pool weights and both
positive Fourier measures are inherited from the actual two sources.
No whole transform identity or source bound is a calibration input.
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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}


variable (p : FirstBlockPoolData chart P M X hX)

def leftSourceCovers (LA : SourceCartesianAtlas left fullI)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    (p.divisorPools.leftData S).SourceCovers (p.leftDivisorCoefficient S χ) :=
  (p.divisorPools.leftData S).sourceCoversOfOriginal
    (p.leftDivisorCoefficient S χ) LA (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns)
    (by
      intro i
      rw [p.divisorPools.left_ideal S, p.left_ideal]
      exact b.left_residual i)

def rightSourceCovers (RA : SourceCartesianAtlas right fullJ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    (p.divisorPools.rightData S).SourceCovers (p.rightDivisorCoefficient S χ) :=
  (p.divisorPools.rightData S).sourceCoversOfOriginal
    (p.rightDivisorCoefficient S χ) RA (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns)
    (by
      intro j
      rw [p.divisorPools.right_ideal S, p.right_ideal]
      exact b.right_residual j)

namespace SecondStages

variable {p}

structure CoverHybridPredicates (s : p.SecondStages (E := E) (hDiff := hDiff))
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ) where
  left : ∀ S χ, (s.left S χ).CoverHybridPredicates (p.leftSourceCovers LA S χ)
  right : ∀ S χ, (s.right S χ).CoverHybridPredicates (p.rightSourceCovers RA S χ)

namespace TerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def coveredCost (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (PUnit × PUnit) →* Circle, ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, (T.left S χ).coverHybridPhaseCost
          (p.leftSourceCovers LA S χ) (exceptional.left S χ)
          chart.leftPoint ξ ε Cerror Czero / NL S χ
          ∂actualFourierMeasure chart.kernel) +
        ∫ ξ, (T.right S χ).coverHybridPhaseCost
          (p.rightSourceCovers RA S χ) (exceptional.right S χ)
          (fun j => -chart.rightPoint j) ξ ε Cerror Czero / NR S χ
          ∂actualFourierMeasure chart.kernel)

theorem rawCost_le_covered
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ) :
    T.rawCost NL NR ε Cerror Czero ≤
      T.coveredCost LA RA exceptional NL NR ε Cerror Czero := by
  unfold rawCost coveredCost
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (norm_nonneg _) (div_nonneg
      (mul_nonneg (mul_nonneg p.rowBound_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (by norm_num)))
  apply add_le_add
  · apply integral_mono
      (((T.left S χ).rawPhaseCost_integrable chart.kernel chart.leftPoint ε Cerror Czero).div_const _)
      (((T.left S χ).coverHybridPhaseCost_integrable
        (p.leftSourceCovers LA S χ) (exceptional.left S χ)
        chart.kernel chart.leftPoint ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      ((T.left S χ).rawPhaseCost_le_coverHybrid
        (p.leftSourceCovers LA S χ) (exceptional.left S χ)
        chart.leftPoint ξ ε Cerror Czero) (hNL S χ).le
  · apply integral_mono
      (((T.right S χ).rawPhaseCost_integrable chart.kernel
        (fun j => -chart.rightPoint j) ε Cerror Czero).div_const _)
      (((T.right S χ).coverHybridPhaseCost_integrable
        (p.rightSourceCovers RA S χ) (exceptional.right S χ)
        chart.kernel (fun j => -chart.rightPoint j) ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      ((T.right S χ).rawPhaseCost_le_coverHybrid
        (p.rightSourceCovers RA S χ) (exceptional.right S χ)
        (fun j => -chart.rightPoint j) ξ ε Cerror Czero) (hNR S χ).le

end TerminalCalibration
end SecondStages
end FirstBlockPoolData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

abbrev CoverHybridPredicates (L : SourceCartesianAtlas s.columns s.ideal) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoverHybridPredicates L L

def coveredCost (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).coveredCost L L (exceptional v D)
      (N.left v D) (N.right v D) ε Cerror Czero

theorem rawCost_le_covered
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (ε Cerror Czero : ℝ) :
    R.rawCost T N ε Cerror Czero ≤
      R.coveredCost T L exceptional N ε Cerror Czero := by
  unfold rawCost coveredCost
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).rawCost_le_covered L L (exceptional v D)
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero

end ActualFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The actual original parent reaches the genuine finite covered
hybrid branches of both transforms.  The original atlas constructs every
residual dictionary; all source zero and tail bounds are internal. -/
theorem actual_parent_two_stage_covered_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
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
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero +
          R.coveredCost T L exceptional N ε Cerror Czero) := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hb⟩ :=
    actual_parent_two_stage_raw_terminal_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s N R T F L exceptional
  obtain ⟨hcutoff, hp⟩ := hb Z ell eps bad P centered d a t Y₁ Y₂ X hX s N R T F
  refine ⟨hcutoff, hp.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (R.rawCost_le_covered T L exceptional N ε Cerror Czero))
    (Nat.cast_nonneg s.fiber)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.leftSourceCovers
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.rightSourceCovers
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_covered_terminal_bound

