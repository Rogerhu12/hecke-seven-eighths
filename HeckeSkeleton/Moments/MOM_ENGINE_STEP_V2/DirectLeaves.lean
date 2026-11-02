import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.DirectStages
set_option linter.unusedSectionVars false

/-!
# Actual canonical leaves of the direct entrance

The first divisor and finite phase precede the actual left/right source
choice. Both direct sources produce the same `ActualHybridLeaf` as the
amplified entrance. Original row multiplicities and normalizers occur
exactly once, with the original double Fourier measure retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
local instance directFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

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

namespace SecondStages

variable (s : FirstBlockDirectData.SecondStages p (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

/-- The actual first internal divisor and finite phase precede the
left/right choice and all genuine second-transform labels. -/
abbrev CoveredClassKey
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :=
  ActualGaussStage.CoveredLeafKey (s.left S χ) (FirstBlockDirectData.leftSourceCover p LA S χ) (FirstBlockDirectData.leftSourceCover p LA S χ) ⊕
    ActualGaussStage.CoveredLeafKey (s.right S χ) (FirstBlockDirectData.rightSourceCover p RA S χ) (FirstBlockDirectData.rightSourceCover p RA S χ)

abbrev CoveredLeafKey :=
  Σ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
    Σ χ : (PUnit × PUnit) →* Circle, FirstBlockDirectData.SecondStages.CoveredClassKey s LA RA S χ

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

def classLeaf (exceptional : FirstBlockDirectData.SecondStages.CoverHybridPredicates s LA RA)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    FirstBlockDirectData.SecondStages.CoveredClassKey s LA RA S χ → ActualHybridLeaf K Q W E
  | .inl j =>
      (ActualGaussStage.fiberCoveredLeaf (s.left S χ) (FirstBlockDirectData.leftSourceCover p LA S χ) (FirstBlockDirectData.leftSourceCover p LA S χ) (exceptional.left S χ)
        chart.kernel chart.leftPoint j).scale
        (classWeight (p := p) NL NR S χ / NL S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)
  | .inr j =>
      (ActualGaussStage.fiberCoveredLeaf (s.right S χ) (FirstBlockDirectData.rightSourceCover p RA S χ) (FirstBlockDirectData.rightSourceCover p RA S χ) (exceptional.right S χ)
        chart.kernel (fun j => -chart.rightPoint j) j).scale
        (classWeight (p := p) NL NR S χ / NR S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le)

def coveredLeaf (exceptional : FirstBlockDirectData.SecondStages.CoverHybridPredicates s LA RA)
    (j : FirstBlockDirectData.SecondStages.CoveredLeafKey s LA RA) : ActualHybridLeaf K Q W E :=
  FirstBlockDirectData.SecondStages.classLeaf s LA RA NL NR hNL hNR exceptional j.1 j.2.1 j.2.2

/-- The original nonsquarefree first divisors are genuinely zero
weight leaves; no squarefreeness premise is imposed on the pool. -/
theorem coveredLeaf_weight_eq_zero_of_not_squarefree
    (exceptional : FirstBlockDirectData.SecondStages.CoverHybridPredicates s LA RA) (j : FirstBlockDirectData.SecondStages.CoveredLeafKey s LA RA)
    (hj : ¬Squarefree j.1.val) :
    (FirstBlockDirectData.SecondStages.coveredLeaf s LA RA NL NR hNL hNR exceptional j).weight = 0 := by
  rcases j with ⟨S, χ, j | j⟩ <;>
    simp only [coveredLeaf, classLeaf, ActualHybridLeaf.scale,
      classWeight_eq_zero_of_not_squarefree NL NR S χ hj, zero_div, zero_mul]

theorem coveredLeaf_weight_nonzero_squarefree
    (exceptional : FirstBlockDirectData.SecondStages.CoverHybridPredicates s LA RA) (j : FirstBlockDirectData.SecondStages.CoveredLeafKey s LA RA)
    (hj : (FirstBlockDirectData.SecondStages.coveredLeaf s LA RA NL NR hNL hNR exceptional j).weight ≠ 0) :
    Squarefree j.1.val := by
  by_contra hS
  exact hj (FirstBlockDirectData.SecondStages.coveredLeaf_weight_eq_zero_of_not_squarefree s LA RA NL NR hNL hNR exceptional j hS)

end SecondStages
end FirstBlockDirectData
end HeckeSkeleton.Moments.EngineStepV2

