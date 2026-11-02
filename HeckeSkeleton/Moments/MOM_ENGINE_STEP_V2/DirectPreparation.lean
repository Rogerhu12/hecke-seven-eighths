import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.DirectParent
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceSupport

/-!
# Genuine live arithmetic support in the direct entrance

The same engine-built source gates retain the original physical rows
and remove empty sources and inactive common labels before estimates.
The first Möbius weight then proves squarefreeness on every retained
leaf. The original first divisor is inherited by both genuine second
common ideals through the original coefficient support.
-/

set_option linter.unusedSectionVars false
set_option quotPrecheck false

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

attribute [local instance] FirstBlockDirectData.SecondStages.coveredClassKeyFintype
  FirstBlockDirectData.SecondStages.coveredLeafKeyFintype

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
local instance directSupportedLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}


namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

theorem leftDivisorCoefficient_nonzero_dvd
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : ι)
    (hi : FirstBlockDirectData.leftDivisorCoefficient p S χ i ≠ 0) : S.val ∣ (p.leftData.ideal i).val := by
  by_contra hn
  exact hi (by simp only [leftDivisorCoefficient, if_neg hn])

theorem rightDivisorCoefficient_nonzero_dvd
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : κ)
    (hi : FirstBlockDirectData.rightDivisorCoefficient p S χ i ≠ 0) : S.val ∣ (p.rightData.ideal i).val := by
  by_contra hn
  exact hi (by simp only [rightDivisorCoefficient, if_neg hn])

namespace SecondStages

variable (s : FirstBlockDirectData.SecondStages p (E := E) (hDiff := hDiff))

def prepared : FirstBlockDirectData.SecondStages p (E := E) (hDiff := hDiff) where
  left S χ := ActualGaussStage.gated (ActualGaussStage.supported (s.left S χ))
  right S χ := ActualGaussStage.gated (ActualGaussStage.supported (s.right S χ))



theorem left_active_common_contains_first_divisor
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : Squarefree S.val)
    (DE : commonSupportPool p.leftData.columns p.leftData.columns
      (fun i => (p.leftData.ideal i).val) (fun j => (p.leftData.ideal j).val))
    (D : (s.left S χ).mask.powerset) (i : ι)
    (hi : (((FirstBlockDirectData.SecondStages.prepared s).left S χ).charts DE D).leftCoefficient i ≠ 0) :
    S.val ∣ DE.val.1 ∧ S.val ∣ DE.val.2 := by
  apply ActualGaussSource.activeCommon_old_mask (p.leftData.directSource (FirstBlockDirectData.leftDivisorCoefficient p S χ))
    S.val hS (fun i _ hi => leftDivisorCoefficient_nonzero_dvd S χ i hi) DE.val
  apply ActualGaussStage.supported_left_nonzero_active (s.left S χ) DE D i
  exact ActualGaussStage.gated_left_nonzero_original (ActualGaussStage.supported (s.left S χ)) DE D i hi

theorem right_active_common_contains_first_divisor
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : Squarefree S.val)
    (DE : commonSupportPool p.rightData.columns p.rightData.columns
      (fun i => (p.rightData.ideal i).val) (fun j => (p.rightData.ideal j).val))
    (D : (s.right S χ).mask.powerset) (i : κ)
    (hi : (((FirstBlockDirectData.SecondStages.prepared s).right S χ).charts DE D).leftCoefficient i ≠ 0) :
    S.val ∣ DE.val.1 ∧ S.val ∣ DE.val.2 := by
  apply ActualGaussSource.activeCommon_old_mask (p.rightData.directSource (FirstBlockDirectData.rightDivisorCoefficient p S χ))
    S.val hS (fun i _ hi => rightDivisorCoefficient_nonzero_dvd S χ i hi) DE.val
  apply ActualGaussStage.supported_left_nonzero_active (s.right S χ) DE D i
  exact ActualGaussStage.gated_left_nonzero_original (ActualGaussStage.supported (s.right S χ)) DE D i hi

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : ActualDirectFirstSource.SecondStages s (E := E) (hDiff := hDiff))

def prepared : ActualDirectFirstSource.SecondStages s (E := E) (hDiff := hDiff) := fun v D => FirstBlockDirectData.SecondStages.prepared (R v D)



variable (L : SourceCartesianAtlas s.columns s.ideal)

def liveLeaves (exceptional : ActualDirectFirstSource.SecondStages.CoverHybridPredicates R L) (N : s.Normalization) :
    Finset (ActualDirectFirstSource.SecondStages.CoveredLeafKey R L) := ActualHybridFamily.live (ActualDirectFirstSource.SecondStages.parentLeaf R L exceptional N)

theorem liveLeaves_spec (exceptional : ActualDirectFirstSource.SecondStages.CoverHybridPredicates R L) (N : s.Normalization)
    (j : ActualDirectFirstSource.SecondStages.liveLeaves R L exceptional N) :
    (ActualDirectFirstSource.SecondStages.parentLeaf R L exceptional N j.val).Live := ActualHybridFamily.live_spec _ j

theorem live_first_divisor_squarefree
    (exceptional : ActualDirectFirstSource.SecondStages.CoverHybridPredicates R L) (N : s.Normalization)
    (j : ActualDirectFirstSource.SecondStages.liveLeaves R L exceptional N) : Squarefree j.val.2.2.1.val := by
  have hw := (ActualDirectFirstSource.SecondStages.liveLeaves_spec R L exceptional N j).1
  change (s.fiber : ℝ) *
    (FirstBlockDirectData.SecondStages.coveredLeaf (R j.val.1 j.val.2.1) L L
      (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
      (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
      (exceptional j.val.1 j.val.2.1) j.val.2.2).weight ≠ 0 at hw
  exact FirstBlockDirectData.SecondStages.coveredLeaf_weight_nonzero_squarefree (R j.val.1 j.val.2.1) L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 (mul_ne_zero_iff.mp hw).2

theorem leaves_cost_eq_live
    (exceptional : ActualDirectFirstSource.SecondStages.CoverHybridPredicates R L) (N : s.Normalization) :
    (∑ j : ActualDirectFirstSource.SecondStages.CoveredLeafKey R L, (ActualDirectFirstSource.SecondStages.parentLeaf R L exceptional N j).cost) =
      (∑ j : ActualDirectFirstSource.SecondStages.liveLeaves R L exceptional N, (ActualDirectFirstSource.SecondStages.parentLeaf R L exceptional N j.val).exceptionalCost) +
      (∑ j : ActualDirectFirstSource.SecondStages.liveLeaves R L exceptional N, (ActualDirectFirstSource.SecondStages.parentLeaf R L exceptional N j.val).ordinaryCost) := by
  rw [ActualHybridFamily.sum_cost_eq_live]
  simp only [ActualHybridLeaf.cost, Finset.sum_add_distrib]

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStepV2


