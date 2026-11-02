import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstGaussData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Constructing the actual first parent source

The parent row-ball test, its whole centered Gram matrix, every common
block, the first logarithmic chart, and both actual Gauss row dictionaries
are constructed from the original single-atom data. The original exterior
Cartesian atlas is retained definitionally. There is no supplied mixed
profile, first profile chart, parent comparison, or Gauss-block record.

The direct source is independent of a prime pool. Attaching an earlier
pool below preserves this exact source and uses only individual original
row, frozen ideal and column norm windows.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

section Pool

variable {hΓ μv}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {centered : Bool} {X : ℝ} {hX : 1 ≤ X}

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := E) hΓ μv C Z
  finiteTest centered d a t Y₁ Y₂ X hX)

/-- The original physical rows and columns supply a pooled entrance
without replacing the actual first chart or its complete parent source.
The positive density for these individual exponent windows follows from
`uniform_pool_density_and_mass` at the earlier fixed threshold. -/
def withOriginalPool
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (frozenLeft frozenRight : Ideal (𝓞 K))
    (hfrozenLeft : frozenLeft ≠ 0) (hfrozenRight : frozenRight ≠ 0)
    (rowLeft rowRight boundLeft boundRight divisorBound : ℝ)
    (hrowLeft : 0 ≤ rowLeft) (hrowRight : 0 ≤ rowRight)
    (hdivisor : 0 ≤ divisorBound)
    (hrowsLeft : ∀ v D, ∀ h ∈ (s.pieces v D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowLeft)
    (hrowsRight : ∀ v D, ∀ h ∈ (s.pieces v D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowRight)
    (hfrozenNormLeft : (Ideal.absNorm frozenLeft : ℝ) ≤ Z ^ boundLeft)
    (hfrozenNormRight : (Ideal.absNorm frozenRight : ℝ) ≤ Z ^ boundRight)
    (hcolumns : ∀ j ∈ s.columns, (Ideal.absNorm (s.ideal j).val : ℝ) ≤ Z ^ divisorBound)
    (hdensityLeft : 0 < P.rowDensity rowLeft (boundLeft + divisorBound))
    (hdensityRight : 0 < P.rowDensity rowRight (boundRight + divisorBound)) :
    ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX where
  Column := s.Column
  columns := s.columns
  ideal := s.ideal
  generator := s.generator
  generates := s.generates
  profiles := s.profiles
  radius := s.radius
  mask := s.mask
  fiber := s.fiber
  charts := s.charts
  pools v D := FirstBlockDirectData.withOriginalPool (s.pieces v D) P frozenLeft frozenRight
    hfrozenLeft hfrozenRight rowLeft rowRight boundLeft boundRight divisorBound
    hrowLeft hrowRight hdivisor (hrowsLeft v D) (hrowsRight v D)
    hfrozenNormLeft hfrozenNormRight hcolumns hdensityLeft hdensityRight
  calibration := s.calibration

end ActualDirectFirstSource
end Pool

end HeckeSkeleton.Moments.EngineStepV2

