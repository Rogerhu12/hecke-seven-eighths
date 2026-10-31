import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportedGaussStages

/-!
# Genuine live arithmetic support in the direct entrance

The same engine-built source gates retain the original physical rows
and remove empty sources and inactive common labels before estimates.
The first Möbius weight then proves squarefreeness on every retained
leaf. The original first divisor is inherited by both genuine second
common ideals through the original coefficient support.
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
local instance directSupportedLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}


namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

theorem leftDivisorCoefficient_nonzero_dvd
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : ι)
    (hi : p.leftDivisorCoefficient S χ i ≠ 0) : S.val ∣ (p.leftData.ideal i).val := by
  by_contra hn
  exact hi (by simp only [leftDivisorCoefficient, if_neg hn])

theorem rightDivisorCoefficient_nonzero_dvd
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : κ)
    (hi : p.rightDivisorCoefficient S χ i ≠ 0) : S.val ∣ (p.rightData.ideal i).val := by
  by_contra hn
  exact hi (by simp only [rightDivisorCoefficient, if_neg hn])

namespace SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))

def prepared : p.SecondStages (E := E) (hDiff := hDiff) where
  left S χ := (s.left S χ).supported.gated
  right S χ := (s.right S χ).supported.gated

namespace TerminalCalibration

variable {s} {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def prepared (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.prepared.TerminalCalibration sTail sZero k Z Lmax Nsave decay where
  left S χ := (T.left S χ).supported.gated
  right S χ := (T.right S χ).supported.gated

end TerminalCalibration

theorem left_active_common_contains_first_divisor
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : Squarefree S.val)
    (DE : commonSupportPool p.leftData.columns p.leftData.columns
      (fun i => (p.leftData.ideal i).val) (fun j => (p.leftData.ideal j).val))
    (D : (s.left S χ).mask.powerset) (i : ι)
    (hi : ((s.prepared.left S χ).charts DE D).leftCoefficient i ≠ 0) :
    S.val ∣ DE.val.1 ∧ S.val ∣ DE.val.2 := by
  apply (p.leftData.directSource (p.leftDivisorCoefficient S χ)).activeCommon_old_mask
    S.val hS (fun i _ hi => leftDivisorCoefficient_nonzero_dvd S χ i hi) DE.val
  apply (s.left S χ).supported_left_nonzero_active DE D i
  exact (s.left S χ).supported.gated_left_nonzero_original DE D i hi

theorem right_active_common_contains_first_divisor
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : Squarefree S.val)
    (DE : commonSupportPool p.rightData.columns p.rightData.columns
      (fun i => (p.rightData.ideal i).val) (fun j => (p.rightData.ideal j).val))
    (D : (s.right S χ).mask.powerset) (i : κ)
    (hi : ((s.prepared.right S χ).charts DE D).leftCoefficient i ≠ 0) :
    S.val ∣ DE.val.1 ∧ S.val ∣ DE.val.2 := by
  apply (p.rightData.directSource (p.rightDivisorCoefficient S χ)).activeCommon_old_mask
    S.val hS (fun i _ hi => rightDivisorCoefficient_nonzero_dvd S χ i hi) DE.val
  apply (s.right S χ).supported_left_nonzero_active DE D i
  exact (s.right S χ).supported.gated_left_nonzero_original DE D i hi

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))

def prepared : s.SecondStages (E := E) (hDiff := hDiff) := fun v D => (R v D).prepared

namespace TerminalCalibration

variable {R} {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def prepared (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    R.prepared.TerminalCalibration sTail sZero k Lmax Nsave decay := fun v D => (T v D).prepared

end TerminalCalibration

variable (L : SourceCartesianAtlas s.columns s.ideal)

def liveLeaves (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    Finset (R.CoveredLeafKey L) := ActualHybridFamily.live (R.parentLeaf L exceptional N)

theorem liveLeaves_spec (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.parentLeaf L exceptional N j.val).Live := ActualHybridFamily.live_spec _ j

theorem live_first_divisor_squarefree
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : Squarefree j.val.2.2.1.val := by
  have hw := (R.liveLeaves_spec L exceptional N j).1
  change (s.fiber : ℝ) *
    ((R j.val.1 j.val.2.1).coveredLeaf L L
      (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
      (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
      (exceptional j.val.1 j.val.2.1) j.val.2.2).weight ≠ 0 at hw
  exact (R j.val.1 j.val.2.1).coveredLeaf_weight_nonzero_squarefree L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 (mul_ne_zero_iff.mp hw).2

theorem leaves_cost_eq_live
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    (∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost) =
      (∑ j : R.liveLeaves L exceptional N, (R.parentLeaf L exceptional N j.val).exceptionalCost) +
      (∑ j : R.liveLeaves L exceptional N, (R.parentLeaf L exceptional N j.val).ordinaryCost) := by
  rw [ActualHybridFamily.sum_cost_eq_live]
  simp only [ActualHybridLeaf.cost, Finset.sum_add_distrib]

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.left_active_common_contains_first_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.leaves_cost_eq_live
