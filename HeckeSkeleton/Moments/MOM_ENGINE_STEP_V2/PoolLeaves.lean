import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolCoverHybridStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CoveredStage
set_option linter.unusedSectionVars false

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

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments

private abbrev pool_sum_sigma_fintype
    {P : Type*} {I₀ : Type*}
    {I₁ : P → Type*} {I₆ : P → Type*} {I₇ : P → Type*}
    [Fintype P] [Fintype I₀]
    [∀ p, Fintype (I₁ p)] [∀ p, Fintype (I₆ p)] [∀ p, Fintype (I₇ p)] :
    Fintype (I₀ ⊕ ((Σ p, I₁ p) ⊕ ((Σ p, I₆ p) ⊕ (Σ p, I₇ p)))) :=
  inferInstance

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
  ActualGaussStage.CoveredLeafKey s.main B.main B.main ⊕
    ((Σ p : P.primes, ActualGaussStage.CoveredLeafKey (s.one p) (B.residual p 1) (B.residual p 1)) ⊕
      ((Σ p : P.primes, ActualGaussStage.CoveredLeafKey (s.six p) (B.residual p 6) (B.residual p 6)) ⊕
        (Σ p : P.primes, ActualGaussStage.CoveredLeafKey (s.seven p) (B.residual p 7) (B.residual p 7))))

abbrev coveredLeafKeyFintype : Fintype (ActualPoolStages.CoveredLeafKey s B) :=
  pool_sum_sigma_fintype
    (P := P.primes)
    (I₀ := ActualGaussStage.CoveredLeafKey s.main B.main B.main)
    (I₁ := fun p => ActualGaussStage.CoveredLeafKey (s.one p) (B.residual p 1) (B.residual p 1))
    (I₆ := fun p => ActualGaussStage.CoveredLeafKey (s.six p) (B.residual p 6) (B.residual p 6))
    (I₇ := fun p => ActualGaussStage.CoveredLeafKey (s.seven p) (B.residual p 7) (B.residual p 7))

attribute [local instance] coveredLeafKeyFintype

def coveredLeaf (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) : ActualPoolStages.CoveredLeafKey s B → ActualHybridLeaf K Q W E
  | .inl b =>
      (ActualGaussStage.fiberCoveredLeaf s.main B.main B.main exceptional.main F x b).scale
        ((4 / d.density) * d.multiplicity)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le) d.multiplicity_nonneg)
  | .inr (.inl ⟨p, b⟩) =>
      (ActualGaussStage.fiberCoveredLeaf (s.one p) (B.residual p 1) (B.residual p 1) (exceptional.one p)
        F (fun i => x i.val) b).scale ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 1)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 1))
  | .inr (.inr (.inl ⟨p, b⟩)) =>
      (ActualGaussStage.fiberCoveredLeaf (s.six p) (B.residual p 6) (B.residual p 6) (exceptional.six p)
        F (fun i => x i.val) b).scale ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 6)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 6))
  | .inr (.inr (.inr ⟨p, b⟩)) =>
      (ActualGaussStage.fiberCoveredLeaf (s.seven p) (B.residual p 7) (B.residual p 7) (exceptional.seven p)
        F (fun i => x i.val) b).scale ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 7)
        (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 7))

@[simp] theorem coveredLeaf_firstKernel (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : ActualPoolStages.CoveredLeafKey s B) :
    (ActualPoolStages.coveredLeaf s B exceptional F x b).firstKernel = F := by
  rcases b with b | (⟨p, b⟩ | (⟨p, b⟩ | ⟨p, b⟩)) <;> rfl

end ActualPoolStages
end HeckeSkeleton.Moments.EngineStepV2

