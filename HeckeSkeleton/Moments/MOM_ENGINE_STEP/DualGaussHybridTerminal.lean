import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussDualRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussHybridTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves

/-!
# Pure-dual second terminals with the original finite hybrid leaves

The proved signed Poisson exit pays the pure dual-frequency zero and
the original tail. The untouched raw nonzero source then follows the
existing ordinary/exceptional partition, original Cartesian covers,
common supports and allocation labels.

The first Fourier phases retain the same two kernels, the same
original `Γ`, and the same `CoveredLeafKey` and `fiberCoveredLeaf`.
The final integral identity separates the two actual terminal budgets
from those literal leaves. Neither the source decomposition nor a
whole-source bound is a new assumption, and no profile-zero condition
is introduced.
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {hΓ μv hDiff}

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
local instance dualGaussHybridTerminalCircleCharacterFintype :
    Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.DualTerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

def hybridCost (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LA RA : SourceCartesianAtlas G.columns G.ideal)
    (exceptional : s.HybridPredicates LA RA) (ε Cerror Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * (Czero * (T.windows.multiplicity * T.zeroAmplitude) *
      Z ^ (T.productExponent * ε) + s.hybridNonzeroCost LA RA exceptional +
    Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

theorem rawCost_le_hybrid
    {LA RA : SourceCartesianAtlas G.columns G.ideal}
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (exceptional : s.HybridPredicates LA RA) (ε Cerror Czero : ℝ) :
    T.rawCost ε Cerror Czero ≤ T.hybridCost LA RA exceptional ε Cerror Czero := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  exact add_le_add
    (add_le_add le_rfl (s.rawNonzeroCost_le_hybrid LA RA exceptional)) le_rfl

def coverHybridCost (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC) (ε Cerror Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * (Czero * (T.windows.multiplicity * T.zeroAmplitude) *
      Z ^ (T.productExponent * ε) + s.coverHybridNonzeroCost LC RC exceptional +
    Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

theorem rawCost_le_coverHybrid
    {LC RC : SourceCartesianCover G.columns G.ideal}
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (exceptional : s.CoverHybridPredicates LC RC) (ε Cerror Czero : ℝ) :
    T.rawCost ε Cerror Czero ≤ T.coverHybridCost LC RC exceptional ε Cerror Czero := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  exact add_le_add
    (add_le_add le_rfl (s.rawNonzeroCost_le_coverHybrid LC RC exceptional)) le_rfl

theorem rawPhaseCost_integrable
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => (T.fourierPhase x ξ).rawCost ε Cerror Czero)
      (actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change Integrable (fun ξ => (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.rawPhaseNonzeroCost x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))) (actualFourierMeasure F)
  exact (((integrable_const _).add (s.rawPhaseNonzeroCost_integrable F x)).add
    (integrable_const _)).const_mul (s.fiber : ℝ)

theorem integral_rawPhaseCost
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).rawCost ε Cerror Czero ∂actualFourierMeasure F) =
      (s.fiber : ℝ) *
        ((actualFourierMeasure F).real Set.univ *
          (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
            Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) +
          ∫ ξ, s.rawPhaseNonzeroCost x ξ ∂actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change (∫ ξ, (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.rawPhaseNonzeroCost x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))
        ∂actualFourierMeasure F) = _
  rw [integral_const_mul,
    integral_add ((integrable_const _).add (s.rawPhaseNonzeroCost_integrable F x)) (integrable_const _),
    integral_add (integrable_const _) (s.rawPhaseNonzeroCost_integrable F x),
    integral_const, integral_const]
  simp only [smul_eq_mul]
  ring

theorem coverHybridPhaseCost_integrable
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
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
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
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

def zeroBudget (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * Czero * (T.windows.multiplicity * T.zeroAmplitude) *
    Z ^ (T.productExponent * ε)

def tailBudget (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)

/-- Exact terminal and nonzero separation on the original second
source.  Neither terminal budget is a new assumed aggregate estimate. -/
theorem phase_cost_eq_budgets_leaves
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero =
      T.zeroBudget ε Czero + T.tailBudget Cerror +
        ∑ b : s.CoveredLeafKey LC RC,
          (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost ξ := by
  change (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) = _
  rw [s.coverHybridPhaseNonzeroCost_eq_leaf_sum LC RC exceptional F x ξ]
  simp only [fiberCoveredLeaf, ActualHybridLeaf.scale_firstPhaseCost,
    zeroBudget, tailBudget, Finset.mul_sum, mul_add, mul_assoc]
  ring

theorem integral_phase_cost_eq_budgets_leaves
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero
        ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ b : s.CoveredLeafKey LC RC, (s.fiberCoveredLeaf LC RC exceptional F x b).cost := by
  letI := actualFourierMeasure_finite F
  simp_rw [T.phase_cost_eq_budgets_leaves LC RC exceptional F x]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun b _ =>
    (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable))]
  rw [integral_const, integral_finsetSum]
  · simp only [smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    exact (s.fiberCoveredLeaf LC RC exceptional F x b).integral_firstPhaseCost
  · intro b _
    exact (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable

end ActualGaussStage.DualTerminalCalibration

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ

/-- The pure-dual terminal estimate followed by the original covered
hybrid row partition. Constants, orders and physical cutoff precede
all moving source data. The only positivity condition is the signed
original-origin tensor; no whole-source bound is an input. -/
theorem actual_gauss_dual_cover_hybrid_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ) {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LC RC : SourceCartesianCover G.columns G.ideal)
      (exceptional : s.CoverHybridPredicates LC RC),
      s.cutoff ≤ Z ^ ξ ∧
        G.energy hDiff ≤ T.coverHybridCost LC RC exceptional ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_gauss_raw_dual_terminal_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ι G s hmask hpositive T LC RC exceptional
  obtain ⟨hcutoff, henergy⟩ := hb Z G s hmask hpositive T
  exact ⟨hcutoff, henergy.trans (T.rawCost_le_coverHybrid exceptional ε Cerror Czero)⟩

/-- The atlas version of the same pure-dual exit. The covering route
above is the direct entry for the original computed source covers. -/
theorem actual_gauss_dual_hybrid_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ) {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LA RA : SourceCartesianAtlas G.columns G.ideal)
      (exceptional : s.HybridPredicates LA RA),
      s.cutoff ≤ Z ^ ξ ∧
        G.energy hDiff ≤ T.hybridCost LA RA exceptional ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_gauss_raw_dual_terminal_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ι G s hmask hpositive T LA RA exceptional
  obtain ⟨hcutoff, henergy⟩ := hb Z G s hmask hpositive T
  exact ⟨hcutoff, henergy.trans (T.rawCost_le_hybrid exceptional ε Cerror Czero)⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.rawCost_le_coverHybrid
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.integral_rawPhaseCost_le_cover
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.integral_phase_cost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_dual_cover_hybrid_terminal_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_dual_hybrid_terminal_bound
