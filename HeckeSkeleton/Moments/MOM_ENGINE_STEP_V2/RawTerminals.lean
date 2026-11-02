import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Literal zero terms and truncation discrepancies

These data use the original transformed source, the physical cutoff,
and the common first Fourier measure. Uniform seminorm bounds are
proved later; no terminal majorant is chosen in this constructor.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup
open WholeAllocation

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
local instance rawTerminalCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _


/-- Coordinates are the genuine zero term and physical tail. -/
abbrev RawTerminalPair := ℝ × ℝ

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

/-- The exact discrepancy at the source's actual physical cutoff. -/
def rawTruncationCost : ℝ :=
  ∑ DE,
    ‖(∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
      ((s.sources DE).pairs i j).maskedSeries
        (sIntegerFiniteTestFunction K A.Sf finiteTest) s.radius s.mask) -
      (s.sources DE).transform μv hDiff finiteTest‖

theorem rawTruncationCost_nonneg : 0 ≤ (ActualGaussStage.rawTruncationCost (s := s)) :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The original first Fourier phase multiplies both source columns.
The same positive measure is used in the two raw terminal integrals. -/
def rawTerminals (F : SchwartzMap W ℂ) (x : ι → W) : RawTerminalPair :=
  ((s.fiber : ℝ) * ∫ ξ,
      (s.withMultiplier (fun i => jointPhase ξ (x i))).rawZeroCost
        ∂actualFourierMeasure F,
    (s.fiber : ℝ) * ∫ ξ,
      (ActualGaussStage.rawTruncationCost (s := (s.withMultiplier (fun i => jointPhase ξ (x i)))))
        ∂actualFourierMeasure F)

theorem rawTerminals_nonneg (F : SchwartzMap W ℂ) (x : ι → W) :
    0 ≤ ((ActualGaussStage.rawTerminals (s := s)) F x).1 ∧ 0 ≤ ((ActualGaussStage.rawTerminals (s := s)) F x).2 := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _)
      (integral_nonneg (fun _ => EngineStep.ActualGaussStage.rawZeroCost_nonneg _))
  · exact mul_nonneg (Nat.cast_nonneg _)
      (integral_nonneg (fun _ => rawTruncationCost_nonneg _))

/-- Integrability is established on the actual coefficient phase orbit. -/
theorem rawTerminal_integrable (F : SchwartzMap W ℂ) (x : ι → W) :
    Integrable
      (fun ξ => (s.withMultiplier (fun i => jointPhase ξ (x i))).rawZeroCost)
        (actualFourierMeasure F) ∧
    Integrable
      (fun ξ => (ActualGaussStage.rawTruncationCost (s := (s.withMultiplier (fun i => jointPhase ξ (x i))))))
        (actualFourierMeasure F) := by
  sorry

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStepV2

