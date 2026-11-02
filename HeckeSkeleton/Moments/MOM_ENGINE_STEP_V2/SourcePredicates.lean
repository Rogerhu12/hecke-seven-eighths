import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CoveredStage

/-!
# The original character determines every exceptional predicate

This finite predicate uses the actual second row, common pattern and
sixth-unit sector. It is fixed before the ordinary restriction, either
rectangle, either Fourier parameter, or any normalized child.
-/

set_option linter.unusedSectionVars false
set_option quotPrecheck false

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
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
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

namespace CanonicalLiteralActualCharacters
section FixedPhases

variable [IsPrincipalIdealRing A.R]

/-- Direct and main sources retain the actual chosen empty-mask unit,
and their pool factor is the original unit ideal. -/
def unamplifiedPhases (firstIdeal : A.Exterior) (firstElement : A.R)
    (hfirst : A.Generates firstIdeal firstElement) :
    CanonicalLiteralPhaseCalibration.FixedPhases A where
  firstIdeal := firstIdeal
  poolIdeal := unitExterior A
  unitIdeal := unitExterior A
  firstElement := firstElement
  poolElement := 1
  unitElement := CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)
  first_generates := hfirst
  pool_generates := unitExterior_generates A
  unit_generates := CanonicalLiteralFixedPhases.emptyDivisorInverse_generates

def amplifiedPhases {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
    (C : A.GeneralArithmeticContext σ η htrace)
    (firstIdeal : A.Exterior) (firstElement : A.R)
    (hfirst : A.Generates firstIdeal firstElement) (p : ExteriorPrime A) (n : ℕ) :
    CanonicalLiteralPhaseCalibration.FixedPhases A where
  firstIdeal := firstIdeal
  poolIdeal := powerIdeal p (2 * n)
  unitIdeal := unitExterior A
  firstElement := firstElement
  poolElement := generator C p ^ (2 * n)
  unitElement := CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)
  first_generates := hfirst
  pool_generates := generator_power_generates C p (2 * n)
  unit_generates := CanonicalLiteralFixedPhases.emptyDivisorInverse_generates

end FixedPhases

end CanonicalLiteralActualCharacters

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (theta : Finset (HeckeCharacter K))

def literalHybridPredicates : s.CoverHybridPredicates LC RC :=
  fun DE D _ _ label _ _ _ _ _ _ h =>
    (ActualSecondCorrelationRows.literalCharacter (S := ((s.charts DE D).actualRows s.mask s.cutoff s.cutoff_one label)))
      C P R F oldMoving correction
      ((SecondBlockProfileChart.originalNonunitPattern (chart := (s.charts DE D))) s.mask s.cutoff s.cutoff_one label)
      ((SecondBlockProfileChart.originalSector (chart := (s.charts DE D))) P s.mask s.cutoff s.cutoff_one label) h ∈ theta

/-- The leaf reads this same predicate without changing its row,
sector, first moving factors, or finite theta set. -/
@[simp] theorem literalHybridPredicates_leaf
    (v : (ActualGaussStage.CoveredClassKey (s := s)) LC RC) (kernel : SchwartzMap W ℂ)
    (point : ι → W) (j : v.AllocationKey) :
    (v.leaf ((ActualGaussStage.literalHybridPredicates (s := s)) LC RC P R F oldMoving correction theta)
      kernel point j).exceptional = fun h =>
      (ActualSecondCorrelationRows.literalCharacter (S := (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel)))
        C P R F oldMoving correction
        ((SecondBlockProfileChart.originalNonunitPattern (chart := v.chart)) s.mask s.cutoff s.cutoff_one v.rowLabel)
        ((SecondBlockProfileChart.originalSector (chart := v.chart)) P s.mask s.cutoff s.cutoff_one v.rowLabel) h ∈ theta := rfl

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStepV2


