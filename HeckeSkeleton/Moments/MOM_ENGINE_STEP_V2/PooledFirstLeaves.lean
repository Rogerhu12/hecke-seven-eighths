import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolLeaves

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-!
# Actual left/right pool leaves of one original first-transform block

The common Möbius divisor and finite phase remain in the carrier before
choosing either actual side.  Its scalar is the original Cauchy
normalization, and is multiplied into each genuine nested-measure leaf.
The only extra premises are positivity of the two selected scales.
-/

noncomputable section
open UniqueFactorizationMonoid
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup

private abbrev first_block_sum_fintype
    {I J : Type*} [Fintype I] [Fintype J] : Fintype (I ⊕ J) :=
  inferInstance

private abbrev first_block_sigma_sigma_fintype
    {I J : Type*} {F : I → J → Type*}
    [Fintype I] [Fintype J] [∀ i j, Fintype (F i j)] :
    Fintype (Σ i, Σ j, F i j) :=
  inferInstance

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
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance firstBlockFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

attribute [local instance] HeckeSkeleton.Moments.EngineStepV2.ActualPoolStages.coveredLeafKeyFintype

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
variable {p : FirstBlockPoolData chart P M X hX}

namespace SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

/-- The actual first internal divisor and finite phase precede the
left/right choice and all genuine pool/second-transform labels. -/
abbrev CoveredClassKey
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :=
  (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ) ⊕
    (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ)

abbrev coveredClassKeyFintype
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    Fintype (s.CoveredClassKey LA RA S χ) :=
  first_block_sum_fintype
    (I := (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ))
    (J := (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ))

attribute [local instance] coveredClassKeyFintype

abbrev CoveredLeafKey :=
  Σ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
    Σ χ : (PUnit × PUnit) →* Circle, s.CoveredClassKey LA RA S χ

abbrev coveredLeafKeyFintype : Fintype (s.CoveredLeafKey LA RA) :=
  first_block_sigma_sigma_fintype
    (I := divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (J := (PUnit × PUnit) →* Circle)
    (F := fun S χ => s.CoveredClassKey LA RA S χ)

attribute [local instance] coveredLeafKeyFintype

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

def classWeight
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  ‖(moebius S.val : ℂ)‖ *
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2)

theorem classWeight_nonneg
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : 0 ≤ classWeight (p := p) NL NR S χ :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg p.rowBound_nonneg (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (by norm_num))

theorem classWeight_eq_zero_of_not_squarefree
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : ¬Squarefree S.val) :
    classWeight (p := p) NL NR S χ = 0 := by
  simp only [classWeight, moebius_of_not_squarefree hS, Int.cast_zero,
    norm_zero, zero_mul]

def classLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    s.CoveredClassKey LA RA S χ → ActualHybridLeaf K Q W E
  | .inl j =>
      ((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
        chart.kernel chart.leftPoint j).scale
        (classWeight (p := p) NL NR S χ / NL S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)
  | .inr j =>
      ((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
        chart.kernel (fun j => -chart.rightPoint j) j).scale
        (classWeight (p := p) NL NR S χ / NR S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le)

def coveredLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA) : ActualHybridLeaf K Q W E :=
  s.classLeaf LA RA NL NR hNL hNR exceptional j.1 j.2.1 j.2.2

/-- The original nonsquarefree first divisors are genuinely zero
weight leaves; no squarefreeness premise is imposed on the pool. -/
theorem coveredLeaf_weight_eq_zero_of_not_squarefree
    (exceptional : s.CoverHybridPredicates LA RA) (j : s.CoveredLeafKey LA RA)
    (hj : ¬Squarefree j.1.val) :
    (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).weight = 0 := by
  rcases j with ⟨S, χ, j | j⟩ <;>
    simp only [coveredLeaf, classLeaf, ActualHybridLeaf.scale,
      classWeight_eq_zero_of_not_squarefree NL NR S χ hj, zero_div, zero_mul]

theorem coveredLeaf_weight_nonzero_squarefree
    (exceptional : s.CoverHybridPredicates LA RA) (j : s.CoveredLeafKey LA RA)
    (hj : (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).weight ≠ 0) :
    Squarefree j.1.val := by
  by_contra hS
  exact hj (s.coveredLeaf_weight_eq_zero_of_not_squarefree LA RA NL NR hNL hNR exceptional j hS)

end SecondStages
end FirstBlockPoolData
end HeckeSkeleton.Moments.EngineStepV2

