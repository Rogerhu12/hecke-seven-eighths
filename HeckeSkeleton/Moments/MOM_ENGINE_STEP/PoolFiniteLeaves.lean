import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolCoverHybridStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves

/-!
# Literal main and valuation-error leaves of the same prime pool

The finite carrier keeps the main tag and all three actual error tags
with their original prime.  Its weights contain exactly one pool
density, the true main multiplicity or local difference weight, and
the actual orbital fibre multiplicity.  The terminal budgets are
computed from the earlier individual source calibrations.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments

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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualPoolStages

variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (B : d.SourceCovers c)

/-- The four summands are the genuine main, valuation-one,
valuation-six and valuation-seven sources.  Every error retains p. -/
abbrev CoveredLeafKey :=
  s.main.CoveredLeafKey B.main B.main ⊕
    ((Σ p : P.primes, (s.one p).CoveredLeafKey (B.residual p 1) (B.residual p 1)) ⊕
      ((Σ p : P.primes, (s.six p).CoveredLeafKey (B.residual p 6) (B.residual p 6)) ⊕
        (Σ p : P.primes, (s.seven p).CoveredLeafKey (B.residual p 7) (B.residual p 7))))

def coveredLeaf (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) : s.CoveredLeafKey B → ActualHybridLeaf K Q W E
  | .inl b =>
      (s.main.fiberCoveredLeaf B.main B.main exceptional.main F x b).scale
        ((4 / d.density) * d.multiplicity)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le) d.multiplicity_nonneg)
  | .inr (.inl ⟨p, b⟩) =>
      ((s.one p).fiberCoveredLeaf (B.residual p 1) (B.residual p 1) (exceptional.one p)
        F (fun i => x i.val) b).scale ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 1)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 1))
  | .inr (.inr (.inl ⟨p, b⟩)) =>
      ((s.six p).fiberCoveredLeaf (B.residual p 6) (B.residual p 6) (exceptional.six p)
        F (fun i => x i.val) b).scale ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 6)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 6))
  | .inr (.inr (.inr ⟨p, b⟩)) =>
      ((s.seven p).fiberCoveredLeaf (B.residual p 7) (B.residual p 7) (exceptional.seven p)
        F (fun i => x i.val) b).scale ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 7)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 7))

@[simp] theorem coveredLeaf_firstKernel (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey B) :
    (s.coveredLeaf B exceptional F x b).firstKernel = F := by
  rcases b with b | (⟨p, b⟩ | (⟨p, b⟩ | ⟨p, b⟩)) <;> rfl

namespace TerminalCalibration

variable {s B}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def zeroBudget (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε Czero : ℝ) : ℝ :=
  (4 / d.density) *
    (d.multiplicity * T.main.zeroBudget ε Czero +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 * (T.one p).zeroBudget ε Czero) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 * (T.six p).zeroBudget ε Czero) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 * (T.seven p).zeroBudget ε Czero))

def tailBudget (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (Cerror : ℝ) : ℝ :=
  (4 / d.density) *
    (d.multiplicity * T.main.tailBudget Cerror +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 * (T.one p).tailBudget Cerror) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 * (T.six p).tailBudget Cerror) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 * (T.seven p).tailBudget Cerror))

/-- Exact one-pool source separation, before integrating the common
first Fourier variable.  All local error weights remain literal. -/
theorem phase_cost_eq_budgets_leaves
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    T.coverHybridPhaseCost B exceptional x ξ ε Cerror Czero =
      T.zeroBudget ε Czero + T.tailBudget Cerror +
        ∑ b : s.CoveredLeafKey B, (s.coveredLeaf B exceptional F x b).firstPhaseCost ξ := by
  unfold coverHybridPhaseCost
  rw [T.main.phase_cost_eq_budgets_leaves B.main B.main exceptional.main F x ξ]
  simp_rw [ActualGaussStage.TerminalCalibration.phase_cost_eq_budgets_leaves (F := F)]
  simp only [zeroBudget, tailBudget, Fintype.sum_sum_type, Fintype.sum_sigma,
    coveredLeaf, ActualHybridLeaf.scale_firstPhaseCost, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, mul_assoc]
  ring

/-- The source's exact finite carrier is independent of ξ.  Each
nonzero term now carries its original positive nested Fourier measure. -/
theorem integral_phase_cost_eq_budgets_leaves
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, T.coverHybridPhaseCost B exceptional x ξ ε Cerror Czero
        ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ b : s.CoveredLeafKey B, (s.coveredLeaf B exceptional F x b).cost := by
  letI := actualFourierMeasure_finite F
  have hi : ∀ b : s.CoveredLeafKey B,
      Integrable (s.coveredLeaf B exceptional F x b).firstPhaseCost (actualFourierMeasure F) := by
    intro b
    simpa only [s.coveredLeaf_firstKernel B exceptional F x b] using
      (s.coveredLeaf B exceptional F x b).firstPhaseCost_integrable
  simp_rw [T.phase_cost_eq_budgets_leaves B exceptional F x]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun b _ => hi b))]
  rw [integral_const, integral_finsetSum]
  · simp only [smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    simpa only [s.coveredLeaf_firstKernel B exceptional F x b] using
      (s.coveredLeaf B exceptional F x b).integral_firstPhaseCost
  · intro b _
    exact hi b

end TerminalCalibration
end ActualPoolStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.phase_cost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.integral_phase_cost_eq_budgets_leaves

