import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectGaussSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves

/-!
# The direct Gauss entrance reaches the same actual finite leaves

Direct enlargement and prime amplification share the complete second
transform. Here the unamplified whole source is transported by the first
Fourier phase, transformed, and flattened into the canonical actual
leaf carrier. Both zero/tail terms use the original physical cutoff.
The source and every finite label precede either continuous parameter.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The same second-transform constants work for a direct original
Gauss source. In particular this theorem does not require a prime pool
or a positive slot, and uses the existing canonical leaf construction. -/
theorem actual_direct_fourier_covered_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ) {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LC RC : SourceCartesianCover G.columns G.ideal)
      (exceptional : s.CoverHybridPredicates LC RC)
      (F : SchwartzMap W ℂ) (x : ι → W),
      s.cutoff ≤ Z ^ ξmax ∧
      (∫ ξ, G.phaseEnergy (hDiff := hDiff) x ξ ∂actualFourierMeasure F) ≤
        (actualFourierMeasure F).real Set.univ *
          (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ b : s.CoveredLeafKey LC RC,
          (s.fiberCoveredLeaf LC RC exceptional F x b).cost := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero,
    hCerror, hCzero, hb⟩ :=
    actual_gauss_cover_hybrid_terminal_bound (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero,
    hCerror, hCzero, ?_⟩
  intro Z ι G s T LC RC exceptional F x
  refine ⟨(hb Z G s T LC RC exceptional).1, ?_⟩
  calc
    _ ≤ ∫ ξ, (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero
        ∂actualFourierMeasure F := by
      apply integral_mono (G.phaseEnergy_integrable (hDiff := hDiff) F x)
        (T.coverHybridPhaseCost_integrable LC RC exceptional F x ε Cerror Czero)
      intro ξ
      exact (hb Z (G.withMultiplier (fun i => jointPhase ξ (x i)))
        (s.withMultiplier (fun i => jointPhase ξ (x i))) (T.fourierPhase x ξ)
        LC RC exceptional).2
    _ = _ := T.integral_phase_cost_eq_budgets_leaves LC RC exceptional F x ε Cerror Czero

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_fourier_covered_terminal_bound
