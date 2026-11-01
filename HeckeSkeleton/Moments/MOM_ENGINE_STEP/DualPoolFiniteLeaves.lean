import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolFiniteLeaves

/-!
# Pure-dual pool budgets on the same original finite leaves

The new terminal calibration is summed over the old physical source
tags. The nonzero terms are exactly the pre-existing `coveredLeaf`s,
whose weights already contain the one pool density, the appropriate
main or local error scalar, and the original orbital fibre.

The final theorem starts from the literal pooled energy and integrates
the proved pure-dual hybrid bound against the original first Fourier
measure. Its finite leaves retain the original nested second measures.
All constants and seminorm orders are selected before the moving pool,
scale, source, and first Fourier parameter.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory HeckePort.Moments

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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
local instance dualPoolFiniteLeavesCircleCharacterFintype :
    Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualPoolStages.DualTerminalCalibration

variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def zeroBudget (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε Czero : ℝ) : ℝ :=
  (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b * (T.tag b).zeroBudget ε Czero

def tailBudget (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (Cerror : ℝ) : ℝ :=
  (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b * (T.tag b).tailBudget Cerror

/-- An explicit expansion for auditing the single density and the
original `1/6/7` weights. The main multiplicity is retained literally. -/
theorem zeroBudget_eq_four_sources
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) (ε Czero : ℝ) :
    T.zeroBudget ε Czero = (4 / d.density) *
      (d.multiplicity * T.main.zeroBudget ε Czero +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 * (T.one p).zeroBudget ε Czero) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 * (T.six p).zeroBudget ε Czero) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 * (T.seven p).zeroBudget ε Czero)) := by
  simp only [zeroBudget, PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    FirstGaussPoolData.tagWeight, tag]
  ring

theorem tailBudget_eq_four_sources
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) (Cerror : ℝ) :
    T.tailBudget Cerror = (4 / d.density) *
      (d.multiplicity * T.main.tailBudget Cerror +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 * (T.one p).tailBudget Cerror) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 * (T.six p).tailBudget Cerror) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 * (T.seven p).tailBudget Cerror)) := by
  simp only [tailBudget, PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    FirstGaussPoolData.tagWeight, tag]
  ring

/-- The existing physical finite carrier is used verbatim. In
particular the prime in an error tag and every covered occurrence
allocation remain part of the leaf. -/
theorem phase_cost_eq_budgets_leaves
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    T.coverHybridPhaseCost B r x ξ ε Cerror Czero =
      T.zeroBudget ε Czero + T.tailBudget Cerror +
        ∑ b : s.CoveredLeafKey B, (s.coveredLeaf B r F x b).firstPhaseCost ξ := by
  unfold coverHybridPhaseCost
  simp_rw [ActualGaussStage.DualTerminalCalibration.phase_cost_eq_budgets_leaves (F := F)]
  simp only [zeroBudget, tailBudget, PoolSourceTag, Fintype.sum_sum_type,
    Fintype.sum_unique, Fintype.sum_sigma, FirstGaussPoolData.tagWeight,
    FirstGaussPoolData.tagPoint, FirstGaussPoolData.SourceCovers.tag,
    ActualPoolStages.CoverHybridPredicates.tag, ActualPoolStages.tag, tag,
    ActualPoolStages.coveredLeaf, ActualHybridLeaf.scale_firstPhaseCost,
    Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc]
  ring

/-- Exact zero/tail/leaf separation under the original first Fourier
measure. Every leaf's own second Fourier measure is unchanged. -/
theorem integral_phase_cost_eq_budgets_leaves
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, T.coverHybridPhaseCost B r x ξ ε Cerror Czero ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ b : s.CoveredLeafKey B, (s.coveredLeaf B r F x b).cost := by
  letI := actualFourierMeasure_finite F
  have hi : ∀ b : s.CoveredLeafKey B,
      Integrable (s.coveredLeaf B r F x b).firstPhaseCost (actualFourierMeasure F) := by
    intro b
    simpa only [s.coveredLeaf_firstKernel B r F x b] using
      (s.coveredLeaf B r F x b).firstPhaseCost_integrable
  simp_rw [T.phase_cost_eq_budgets_leaves B r F x]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun b _ => hi b))]
  rw [integral_const, integral_finsetSum]
  · simp only [smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    simpa only [s.coveredLeaf_firstKernel B r F x b] using
      (s.coveredLeaf B r F x b).integral_firstPhaseCost
  · intro b _
    exact hi b

end ActualPoolStages.DualTerminalCalibration

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ

/-- The original pooled energy reaches the same finite nested-measure
leaves. All terminal estimates are supplied by the proved pure-dual
transform, not by per-leaf or aggregate bound assumptions. -/
theorem actual_pool_dual_covered_leaf_integral_bound
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
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ι : Type*} (d : FirstGaussPoolData C P ι) (c : ι → ℂ),
    ∀ s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest,
    ∀ hs : s.DualSourceConditions,
    ∀ T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
      (F : SchwartzMap W ℂ) (x : ι → W),
      (∫ ξ, d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ∂actualFourierMeasure F) ≤
        (actualFourierMeasure F).real Set.univ * (T.zeroBudget ε Czero + T.tailBudget Cerror) +
          ∑ b : s.CoveredLeafKey B, (s.coveredLeaf B r F x b).cost := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_pool_dual_cover_hybrid_fourier_stage_bound
      (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ι d c s hs T B r F x
  have hb' := integral_mono (d.twisted_integrable F c x)
    (T.coverHybridPhaseCost_integrable B r F x ε Cerror Czero)
    (fun ξ => hb Z ell eps bad P d c x s hs T B r ξ)
  exact hb'.trans_eq (T.integral_phase_cost_eq_budgets_leaves B r F x ε Cerror Czero)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.zeroBudget_eq_four_sources
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.phase_cost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.integral_phase_cost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_dual_covered_leaf_integral_bound
