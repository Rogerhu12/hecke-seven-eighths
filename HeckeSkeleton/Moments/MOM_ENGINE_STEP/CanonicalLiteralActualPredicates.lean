import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves

/-!
# The original character determines every exceptional predicate

This finite predicate uses the actual second row, common pattern and
sixth-unit sector. It is fixed before the ordinary restriction, either
rectangle, either Fourier parameter, or any normalized child.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

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
    ((s.charts DE D).actualRows s.mask s.cutoff s.cutoff_one label).literalCharacter
      C P R F oldMoving correction
      ((s.charts DE D).originalNonunitPattern s.mask s.cutoff s.cutoff_one label)
      ((s.charts DE D).originalSector P s.mask s.cutoff s.cutoff_one label) h ∈ theta

/-- The leaf reads this same predicate without changing its row,
sector, first moving factors, or finite theta set. -/
@[simp] theorem literalHybridPredicates_leaf
    (v : s.CoveredClassKey LC RC) (kernel : SchwartzMap W ℂ)
    (point : ι → W) (j : v.AllocationKey) :
    (v.leaf (s.literalHybridPredicates LC RC P R F oldMoving correction theta)
      kernel point j).exceptional = fun h =>
      (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).literalCharacter
        C P R F oldMoving correction
        (v.chart.originalNonunitPattern s.mask s.cutoff s.cutoff_one v.rowLabel)
        (v.chart.originalSector P s.mask s.cutoff s.cutoff_one v.rowLabel) h ∈ theta := rfl

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.literalHybridPredicates
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.literalHybridPredicates_leaf
