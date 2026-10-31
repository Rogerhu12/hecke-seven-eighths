import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussCoverHybridTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHybridResidual
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RawSourcePhaseIntegral

/-!
# The original first Fourier measure controls every covered second source

All cover labels and both kernel profiles precede the first Fourier
variable.  The literal unit Gram multiplier moves through the actual
second chart coefficients.  Every resulting hybrid branch is
integrable against the original first Fourier measure, including its
whole centered exceptional row product.  No moving-profile norm bound
or finite continuous Fourier support is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.Moments

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
local notation "Arch" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ


namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

/-- A retained true Cartesian branch has a literal first unit phase on
each complete original coefficient.  Its second kernel and its full
physical row carrier stay fixed. -/
theorem phase_hybridClassCost_integrable
    (F : SchwartzMap W ℂ) (x : ι → W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (label : Fin ((s.charts DE D).rowLabelCount + 1))
    {left₀ right₀ : Finset ι} {k l : ℕ}
    (L : CartesianSourceReindex left₀
      (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
        DE.val DE.property).leftResidual k)
    (R : CartesianSourceReindex right₀
      (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
        DE.val DE.property).rightResidual l)
    (exceptional : ∀ S : Ideal (𝓞 K), ((PUnit × PUnit) →* Circle) →
      (primeSupport S → Finset (Fin (k + 2))) →
      (primeSupport S → Finset (Fin (l + 2))) → Q → Prop) :
    Integrable (fun ξ : W =>
      ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).
        hybridClassCost s.mask s.cutoff s.cutoff_one label L R exceptional)
      (actualFourierMeasure F) := by
  let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
    DE.val DE.property
  let chart := s.charts DE D
  let rows := chart.actualRows s.mask s.cutoff s.cutoff_one label
  have hi := actual_second_hybrid_first_phase_integrable (σ := σ) PUnit
    F chart.kernel rows.rows rows.frequency
    L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots
    b.commonLeftIdeal b.commonRightIdeal
    (fun i => b.leftResidual (L.index i)) (fun j => b.rightResidual (R.index j))
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle)) rows.weight
    (fun i => chart.sourceLeftCoefficient (L.index i))
    (fun j => chart.sourceRightCoefficient (R.index j))
    (fun i => x (L.index i)) (fun j => x (R.index j))
    (fun h i => chart.leftPoint h (L.index i))
    (fun h j => chart.rightPoint h (R.index j)) exceptional
  apply hi.congr
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only [SecondBlockProfileChart.hybridClassCost]
    congr 1 <;> funext i <;>
      dsimp only [SecondBlockProfileChart.sourceLeftCoefficient,
        SecondBlockProfileChart.sourceRightCoefficient, withMultiplier, chart] <;>
      ring

variable (LC RC : SourceCartesianCover G.columns G.ideal)

def coverHybridPhaseNonzeroCost (exceptional : s.CoverHybridPredicates LC RC)
    (x : ι → W) (ξ : W) : ℝ :=
  (s.withMultiplier (fun i => jointPhase ξ (x i))).coverHybridNonzeroCost
    LC RC exceptional

/-- All actual first and second occurrence-label sums remain explicit
and are finite before either Fourier variable. -/
theorem coverHybridPhaseNonzeroCost_integrable
    (F : SchwartzMap W ℂ) (x : ι → W)
    (exceptional : s.CoverHybridPredicates LC RC) :
    Integrable (s.coverHybridPhaseNonzeroCost LC RC exceptional x)
      (actualFourierMeasure F) := by
  unfold coverHybridPhaseNonzeroCost coverHybridNonzeroCost
    SecondBlockProfileChart.coverHybridCost
    SecondBlockProfileChart.subsetHybridCost
    SecondBlockProfileChart.subsetHybridClassCost
  apply integrable_finsetSum
  intro DE _
  apply integrable_finsetSum
  intro D _
  apply integrable_finsetSum
  intro a _
  apply integrable_finsetSum
  intro e _
  apply integrable_finsetSum
  intro label _
  apply integrable_finsetSum
  intro b _
  apply integrable_finsetSum
  intro f _
  exact s.phase_hybridClassCost_integrable F x DE D label _ _ (exceptional DE D a e label b f)

/-- The actual raw second source can be replaced under the first
positive Fourier measure by its genuine cover hybrid cost. -/
theorem integral_rawPhaseNonzeroCost_le_cover
    (F : SchwartzMap W ℂ) (x : ι → W)
    (exceptional : s.CoverHybridPredicates LC RC) :
    (∫ ξ, s.rawPhaseNonzeroCost x ξ ∂actualFourierMeasure F) ≤
      ∫ ξ, s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ ∂actualFourierMeasure F := by
  apply integral_mono
    (s.rawPhaseNonzeroCost_integrable F x)
    (s.coverHybridPhaseNonzeroCost_integrable LC RC F x exceptional)
  intro ξ
  exact (s.withMultiplier (fun i => jointPhase ξ (x i))).
    rawNonzeroCost_le_coverHybrid LC RC exceptional

namespace TerminalCalibration

variable {s LC RC}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

theorem coverHybridPhaseCost_integrable
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero)
      (actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change Integrable (fun ξ => (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))) (actualFourierMeasure F)
  exact (((integrable_const _).add
    (s.coverHybridPhaseNonzeroCost_integrable LC RC F x exceptional)).add
    (integrable_const _)).const_mul (s.fiber : ℝ)

theorem integral_rawPhaseCost_le_cover
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).rawCost ε Cerror Czero ∂actualFourierMeasure F) ≤
      ∫ ξ, (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero
        ∂actualFourierMeasure F := by
  apply integral_mono (T.rawPhaseCost_integrable F x ε Cerror Czero)
    (T.coverHybridPhaseCost_integrable LC RC exceptional F x ε Cerror Czero)
  intro ξ
  exact (T.fourierPhase x ξ).rawCost_le_coverHybrid exceptional ε Cerror Czero

end TerminalCalibration
end ActualGaussStage

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.phase_hybridClassCost_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.integral_rawPhaseNonzeroCost_le_cover
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.TerminalCalibration.integral_rawPhaseCost_le_cover

