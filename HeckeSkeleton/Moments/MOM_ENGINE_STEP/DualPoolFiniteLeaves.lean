import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolFiniteLeaves

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

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

private theorem dual_pool_scalar_four_tag_sum
    {P : Type*} [Fintype P]
    (a : ℝ) (f : Unit ⊕ (P ⊕ (P ⊕ P)) → ℝ) :
    a * ∑ b, f b =
      a * (f (.inl ()) + (∑ p, f (.inr (.inl p))) +
        (∑ p, f (.inr (.inr (.inl p)))) +
        (∑ p, f (.inr (.inr (.inr p))))) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  ring

private theorem dual_pool_scalar_terminal_sum
    {P : Type*} {I₀ : Type*}
    {I₁ : P → Type*} {I₆ : P → Type*} {I₇ : P → Type*}
    [Fintype P] [Fintype I₀]
    [∀ p, Fintype (I₁ p)] [∀ p, Fintype (I₆ p)] [∀ p, Fintype (I₇ p)]
    (a m : ℝ) (w₁ w₆ w₇ : P → ℝ) (z₀ t₀ : ℝ)
    (z₁ t₁ z₆ t₆ z₇ t₇ : P → ℝ)
    (f₀ : I₀ → ℝ) (f₁ : ∀ p, I₁ p → ℝ)
    (f₆ : ∀ p, I₆ p → ℝ) (f₇ : ∀ p, I₇ p → ℝ)
    (phase : Unit ⊕ (P ⊕ (P ⊕ P)) → ℝ)
    (leaves : I₀ ⊕ ((Σ p, I₁ p) ⊕ ((Σ p, I₆ p) ⊕ (Σ p, I₇ p))) → ℝ)
    (zero tail : ℝ)
    (hphase₀ : phase (.inl ()) = m * (z₀ + t₀ + ∑ b, f₀ b))
    (hphase₁ : ∀ p, phase (.inr (.inl p)) = w₁ p * (z₁ p + t₁ p + ∑ b, f₁ p b))
    (hphase₆ : ∀ p, phase (.inr (.inr (.inl p))) =
      w₆ p * (z₆ p + t₆ p + ∑ b, f₆ p b))
    (hphase₇ : ∀ p, phase (.inr (.inr (.inr p))) =
      w₇ p * (z₇ p + t₇ p + ∑ b, f₇ p b))
    (h₀ : ∀ b, leaves (.inl b) = (a * m) * f₀ b)
    (h₁ : ∀ p b, leaves (.inr (.inl ⟨p, b⟩)) = (a * w₁ p) * f₁ p b)
    (h₆ : ∀ p b, leaves (.inr (.inr (.inl ⟨p, b⟩))) = (a * w₆ p) * f₆ p b)
    (h₇ : ∀ p b, leaves (.inr (.inr (.inr ⟨p, b⟩))) = (a * w₇ p) * f₇ p b)
    (hzero : zero = a * (m * z₀ + (∑ p, w₁ p * z₁ p) +
      (∑ p, w₆ p * z₆ p) + (∑ p, w₇ p * z₇ p)))
    (htail : tail = a * (m * t₀ + (∑ p, w₁ p * t₁ p) +
      (∑ p, w₆ p * t₆ p) + (∑ p, w₇ p * t₇ p))) :
    a * ∑ b, phase b = zero + tail + ∑ b, leaves b := by
  rw [hzero, htail, dual_pool_scalar_four_tag_sum a phase]
  simp only [hphase₀, hphase₁, hphase₆, hphase₇,
    Fintype.sum_sum_type, Fintype.sum_sigma, h₀, h₁, h₆, h₇,
    Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc]
  ring

private theorem dual_pool_scalar_integral_const_add_sum
    {X J : Type*} [MeasurableSpace X] [Fintype J]
    (μ : Measure X) [IsFiniteMeasure μ]
    (c : ℝ) (f : X → ℝ) (leaves : J → X → ℝ) (costs : J → ℝ)
    (leafMeasures : J → Measure X)
    (hpoint : ∀ ξ, f ξ = c + ∑ b : J, leaves b ξ)
    (hmeasure : ∀ b : J, leafMeasures b = μ)
    (hterms : ∀ b : J, Integrable (leaves b) (leafMeasures b))
    (hcosts : ∀ b : J, (∫ ξ, leaves b ξ ∂(leafMeasures b)) = costs b) :
    (∫ ξ, f ξ ∂μ) = μ.real Set.univ * c + ∑ b : J, costs b := by
  have hterms' : ∀ b : J, Integrable (leaves b) μ :=
    fun b => (hmeasure b) ▸ hterms b
  have hcosts' : ∀ b : J, (∫ ξ, leaves b ξ ∂μ) = costs b :=
    fun b => (hmeasure b) ▸ hcosts b
  calc
    (∫ ξ, f ξ ∂μ) = ∫ ξ, c + ∑ b : J, leaves b ξ ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ _ : X, c ∂μ) + ∫ ξ, ∑ b : J, leaves b ξ ∂μ :=
      integral_add (integrable_const c)
        (integrable_finsetSum Finset.univ (fun b _ => hterms' b))
    _ = μ.real Set.univ * c + ∑ b : J, ∫ ξ, leaves b ξ ∂μ := by
      simpa only [integral_const, smul_eq_mul] using
        congrArg (fun z : ℝ => (∫ _ : X, c ∂μ) + z)
          (integral_finsetSum (μ := μ) (f := leaves) Finset.univ
            (fun b _ => hterms' b))
    _ = μ.real Set.univ * c + ∑ b : J, costs b :=
      congrArg (fun z : ℝ => μ.real Set.univ * c + z)
        (Finset.sum_congr rfl (fun b _ => hcosts' b))

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

attribute [local instance] ActualPoolStages.coveredLeafKeyFintype

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
  exact dual_pool_scalar_four_tag_sum
    (P := P.primes) (4 / d.density)
    (fun b : PoolSourceTag P => d.tagWeight b * (T.tag b).zeroBudget ε Czero)

theorem tailBudget_eq_four_sources
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) (Cerror : ℝ) :
    T.tailBudget Cerror = (4 / d.density) *
      (d.multiplicity * T.main.tailBudget Cerror +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 * (T.one p).tailBudget Cerror) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 * (T.six p).tailBudget Cerror) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 * (T.seven p).tailBudget Cerror)) := by
  exact dual_pool_scalar_four_tag_sum
    (P := P.primes) (4 / d.density)
    (fun b : PoolSourceTag P => d.tagWeight b * (T.tag b).tailBudget Cerror)

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
  exact dual_pool_scalar_terminal_sum
    (P := P.primes)
    (I₀ := s.main.CoveredLeafKey B.main B.main)
    (I₁ := fun p => (s.one p).CoveredLeafKey (B.residual p 1) (B.residual p 1))
    (I₆ := fun p => (s.six p).CoveredLeafKey (B.residual p 6) (B.residual p 6))
    (I₇ := fun p => (s.seven p).CoveredLeafKey (B.residual p 7) (B.residual p 7))
    (4 / d.density) d.multiplicity
    (fun p => FirstGaussPoolData.localErrorWeight p.val 1)
    (fun p => FirstGaussPoolData.localErrorWeight p.val 6)
    (fun p => FirstGaussPoolData.localErrorWeight p.val 7)
    (T.main.zeroBudget ε Czero) (T.main.tailBudget Cerror)
    (fun p => (T.one p).zeroBudget ε Czero) (fun p => (T.one p).tailBudget Cerror)
    (fun p => (T.six p).zeroBudget ε Czero) (fun p => (T.six p).tailBudget Cerror)
    (fun p => (T.seven p).zeroBudget ε Czero) (fun p => (T.seven p).tailBudget Cerror)
    (fun b => (s.main.fiberCoveredLeaf B.main B.main r.main F x b).firstPhaseCost ξ)
    (fun p b => ((s.one p).fiberCoveredLeaf (B.residual p 1) (B.residual p 1)
      (r.one p) F (fun i => x i.val) b).firstPhaseCost ξ)
    (fun p b => ((s.six p).fiberCoveredLeaf (B.residual p 6) (B.residual p 6)
      (r.six p) F (fun i => x i.val) b).firstPhaseCost ξ)
    (fun p b => ((s.seven p).fiberCoveredLeaf (B.residual p 7) (B.residual p 7)
      (r.seven p) F (fun i => x i.val) b).firstPhaseCost ξ)
    (fun b : PoolSourceTag P => d.tagWeight b *
      ((T.tag b).fourierPhase (d.tagPoint x b) ξ).coverHybridCost
        (B.tag b) (B.tag b) (r.tag b) ε Cerror Czero)
    (fun b => (s.coveredLeaf B r F x b).firstPhaseCost ξ)
    (T.zeroBudget ε Czero) (T.tailBudget Cerror)
    (congrArg (fun z : ℝ => d.multiplicity * z)
      (T.main.phase_cost_eq_budgets_leaves B.main B.main r.main F x ξ ε Cerror Czero))
    (fun p => congrArg (fun z : ℝ => FirstGaussPoolData.localErrorWeight p.val 1 * z)
      ((T.one p).phase_cost_eq_budgets_leaves (B.residual p 1) (B.residual p 1)
        (r.one p) F (fun i => x i.val) ξ ε Cerror Czero))
    (fun p => congrArg (fun z : ℝ => FirstGaussPoolData.localErrorWeight p.val 6 * z)
      ((T.six p).phase_cost_eq_budgets_leaves (B.residual p 6) (B.residual p 6)
        (r.six p) F (fun i => x i.val) ξ ε Cerror Czero))
    (fun p => congrArg (fun z : ℝ => FirstGaussPoolData.localErrorWeight p.val 7 * z)
      ((T.seven p).phase_cost_eq_budgets_leaves (B.residual p 7) (B.residual p 7)
        (r.seven p) F (fun i => x i.val) ξ ε Cerror Czero))
    (fun b => (s.main.fiberCoveredLeaf B.main B.main r.main F x b).scale_firstPhaseCost
      ((4 / d.density) * d.multiplicity)
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le) d.multiplicity_nonneg) ξ)
    (fun p b => ((s.one p).fiberCoveredLeaf (B.residual p 1) (B.residual p 1)
      (r.one p) F (fun i => x i.val) b).scale_firstPhaseCost
      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 1)
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)) ξ)
    (fun p b => ((s.six p).fiberCoveredLeaf (B.residual p 6) (B.residual p 6)
      (r.six p) F (fun i => x i.val) b).scale_firstPhaseCost
      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 6)
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)) ξ)
    (fun p b => ((s.seven p).fiberCoveredLeaf (B.residual p 7) (B.residual p 7)
      (r.seven p) F (fun i => x i.val) b).scale_firstPhaseCost
      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 7)
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)) ξ)
    (T.zeroBudget_eq_four_sources ε Czero)
    (T.tailBudget_eq_four_sources Cerror)

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
  exact dual_pool_scalar_integral_const_add_sum
    (X := W) (J := s.CoveredLeafKey B)
    (actualFourierMeasure F)
    (T.zeroBudget ε Czero + T.tailBudget Cerror)
    (fun ξ => T.coverHybridPhaseCost B r x ξ ε Cerror Czero)
    (fun b => (s.coveredLeaf B r F x b).firstPhaseCost)
    (fun b => (s.coveredLeaf B r F x b).cost)
    (fun b => actualFourierMeasure (s.coveredLeaf B r F x b).firstKernel)
    (fun ξ => T.phase_cost_eq_budgets_leaves B r F x ξ ε Cerror Czero)
    (fun b => congrArg (fun H : SchwartzMap W ℂ => actualFourierMeasure H)
      (s.coveredLeaf_firstKernel B r F x b))
    (fun b => (s.coveredLeaf B r F x b).firstPhaseCost_integrable)
    (fun b => (s.coveredLeaf B r F x b).integral_firstPhaseCost)

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
