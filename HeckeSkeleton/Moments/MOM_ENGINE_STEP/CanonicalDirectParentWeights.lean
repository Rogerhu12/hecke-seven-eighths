import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOrdinaryWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafArithmetic

/-!
# Canonical direct first allowances and the literal parent weight

The normalization is computed from the original first common pair.
The complete parent scalar includes its original orbital fibre, the
first Cauchy half, the original literal direct-stage fibre, the second
orbital fibre, and both independent divisor and phase coefficients.

The formulas are exact on the original dependent source carrier and
remain exact after constant common-atom extraction. They provide the
outer identity required by the same-child pointwise mass theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData.SecondStages

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}
variable (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def firstAllowanceAt (total : ℝ) (j : R.CoveredLeafKey LA RA) : ℝ :=
  match j.2.2 with
  | .inl _ => firstLeftAllowance Z total DE.1 DE.2
  | .inr _ => firstRightAllowance Z total DE.1 DE.2

/-- This is the actual second orbital fibre. No pool data occurs. -/
def directScalarAt (j : R.CoveredLeafKey LA RA) : ℝ :=
  match j.2.2 with
  | .inl _ => ((R.left j.1 j.2.1).fiber : ℝ)
  | .inr _ => ((R.right j.1 j.2.1).fiber : ℝ)

def secondPhaseAt (j : R.CoveredLeafKey LA RA) : (PUnit × PUnit) →* Circle :=
  match j.2.2 with
  | .inl a => a.2.2.1
  | .inr a => a.2.2.1

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

theorem coveredLeaf_weight_original_relative
    (exceptional : R.CoverHybridPredicates LA RA)
    (parentWidth total : ℝ)
    (hleftScale : ∀ S χ, NL S χ = firstLeftAllowance Z total DE.1 DE.2)
    (hrightScale : ∀ S χ, NR S χ = firstRightAllowance Z total DE.1 DE.2)
    (j : R.CoveredLeafKey LA RA) :
    (R.coveredLeaf LA RA NL NR hNL hNR exceptional j).weight / Z ^ parentWidth =
      (R.directScalarAt LA RA j / 2) *
        (firstOriginalAllowanceWeight Z parentWidth total p.weightBound DE.1 DE.2 *
          ‖(moebius j.1.val : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) j.2.1‖ *
          ‖(moebius (R.innerDivisor LA RA j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            (R.secondPhaseAt LA RA j)‖) /
        R.firstAllowanceAt LA RA total j := by
  rcases j with ⟨S, χ, j | j⟩ <;>
    simp only [coveredLeaf, classLeaf, ActualHybridLeaf.scale,
      ActualGaussStage.fiberCoveredLeaf, ActualGaussStage.coveredLeaf,
      ActualGaussStage.CoveredClassKey.leaf_weight_original,
      classWeight, FirstBlockDirectData.rowBound,
      hleftScale S χ, hrightScale S χ, b.activeNorm_eq, firstOriginalAllowanceWeight,
      directScalarAt, secondPhaseAt, firstAllowanceAt, innerDivisor] <;> ring

end FirstBlockDirectData.SecondStages

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource

/-- The direct entrance computes the same original first allowances,
with no prime-pool parameter or slot-count restriction. -/
def canonicalNormalization
    (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
    (hZ : 1 < Z)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) : s.Normalization where
  left v D _ _ := firstLeftAllowance Z (total v D) v.val.1 v.val.2
  right v D _ _ := firstRightAllowance Z (total v D) v.val.1 v.val.2
  left_pos v D _ _ := firstLeftAllowance_pos Z _ (zero_lt_one.trans hZ) _ _
  right_pos v D _ _ := firstRightAllowance_pos Z _ (zero_lt_one.trans hZ) _ _

end ActualDirectFirstSource

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)

def firstAllowanceAt (j : R.CoveredLeafKey L) : ℝ :=
  (R j.1 j.2.1).firstAllowanceAt L L (total j.1 j.2.1) j.2.2

def originalScalarAt (j : R.CoveredLeafKey L) : ℝ :=
  (s.fiber : ℝ) * (R j.1 j.2.1).directScalarAt L L j.2.2 / 2

def secondPhaseAt (j : R.CoveredLeafKey L) : (PUnit × PUnit) →* Circle :=
  (R j.1 j.2.1).secondPhaseAt L L j.2.2

/-- The original first normalization is constructed internally. All
quantities on the right are projections of this same parent leaf. -/
theorem parentLeaf_weight_original_relative
    (exceptional : R.CoverHybridPredicates L) (parentWidth : ℝ)
    (j : R.CoveredLeafKey L) :
    (R.parentLeaf L exceptional (s.canonicalNormalization hZ total) j).weight /
        Z ^ parentWidth =
      R.originalScalarAt L j *
        (firstOriginalAllowanceWeight Z parentWidth (total j.1 j.2.1)
          (s.pieces j.1 j.2.1).weightBound j.1.val.1 j.1.val.2 *
          ‖(moebius j.2.2.1.val : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) j.2.2.2.1‖ *
          ‖(moebius (R.innerDivisor L j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            (R.secondPhaseAt L j)‖) /
        R.firstAllowanceAt L total j := by
  have hb := (R j.1 j.2.1).coveredLeaf_weight_original_relative L L
    ((s.canonicalNormalization hZ total).left j.1 j.2.1)
    ((s.canonicalNormalization hZ total).right j.1 j.2.1)
    ((s.canonicalNormalization hZ total).left_pos j.1 j.2.1)
    ((s.canonicalNormalization hZ total).right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) parentWidth (total j.1 j.2.1)
    (fun _ _ => rfl) (fun _ _ => rfl) j.2.2
  change ((s.fiber : ℝ) *
    ((R j.1 j.2.1).coveredLeaf L L
      ((s.canonicalNormalization hZ total).left j.1 j.2.1)
      ((s.canonicalNormalization hZ total).right j.1 j.2.1)
      ((s.canonicalNormalization hZ total).left_pos j.1 j.2.1)
      ((s.canonicalNormalization hZ total).right_pos j.1 j.2.1)
      (exceptional j.1 j.2.1) j.2.2).weight) / Z ^ parentWidth = _
  calc
    _ = (s.fiber : ℝ) *
        (((R j.1 j.2.1).coveredLeaf L L
          ((s.canonicalNormalization hZ total).left j.1 j.2.1)
          ((s.canonicalNormalization hZ total).right j.1 j.2.1)
          ((s.canonicalNormalization hZ total).left_pos j.1 j.2.1)
          ((s.canonicalNormalization hZ total).right_pos j.1 j.2.1)
          (exceptional j.1 j.2.1) j.2.2).weight / Z ^ parentWidth) := by ring
    _ = _ := by
      rw [hb]
      dsimp only [originalScalarAt, firstAllowanceAt, secondPhaseAt, innerDivisor]
      ring

/-- Extracting the proved constant common atoms preserves the same
parent scalar, including its first orbital fibre. -/
theorem extracted_parentLeaf_weight_original_relative
    (exceptional : R.CoverHybridPredicates L) (parentWidth : ℝ)
    (j : R.CoveredLeafKey L)
    (extract :
      (R.parentLeaf L exceptional (s.canonicalNormalization hZ total) j).ConstantAtomExtraction) :
    extract.leaf.weight / Z ^ parentWidth =
      R.originalScalarAt L j *
        (firstOriginalAllowanceWeight Z parentWidth (total j.1 j.2.1)
          (s.pieces j.1 j.2.1).weightBound j.1.val.1 j.1.val.2 *
          ‖(moebius j.2.2.1.val : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) j.2.2.2.1‖ *
          ‖(moebius (R.innerDivisor L j) : ℂ)‖ *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))
            (R.secondPhaseAt L j)‖) /
        R.firstAllowanceAt L total j := by
  rw [extract.weight_eq]
  exact R.parentLeaf_weight_original_relative L hZ total exceptional parentWidth j

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.coveredLeaf_weight_original_relative
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.parentLeaf_weight_original_relative
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.extracted_parentLeaf_weight_original_relative

