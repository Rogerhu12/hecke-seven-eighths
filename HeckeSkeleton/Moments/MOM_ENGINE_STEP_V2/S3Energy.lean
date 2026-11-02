import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3ExpansionData
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.ProbeRowCharacters

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One-pool energy comparison for the whole original coefficient

The base finite amplifier is applied at each first Fourier parameter,
then integrated against the identical first kernel. Finite reindexing
charges every main and valuation term exactly once.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance energyValuationFintype : Fintype AmplifierValuation where
  elems := {.one, .six, .seven}
  complete e := by cases e <;> simp

theorem sum_branch {α : Type} [Fintype α]
    (f : Unit ⊕ (α × AmplifierValuation) → ℝ) :
    (∑ key, f key) = f (.inl ()) +
      ∑ q, (f (.inr (q, .one)) + f (.inr (q, .six)) + f (.inr (q, .seven))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, sum_valuation]

/-- The original arithmetic context supplies the four literal CRT
recipes required by the finite amplifier. The unused theta field plays
no part in this dictionary. -/
theorem exists_coefficient_recipes {A : SArithmeticData K} {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    (C : A.GeneralArithmeticContext σ η hS) :
    ∃ D : ComparisonPoissonCoefficientData K A,
      GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D := by
  let r (I : A.Exterior) : A.R := Classical.choose (C.allowed_integral I)
  have hr (I : A.Exterior) : A.Generates I (r I) :=
    (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).1
  let e : AddChar K ℂ :=
    { toFun := fun x => (A.fieldTraceCharacter x : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro x y
        exact congrArg Circle.coeHom (A.fieldTraceCharacter.map_add_eq_mul x y) }
  let D : ComparisonPoissonCoefficientData K A :=
    { generator := r
      generates := hr
      finiteResidue := PrincipalProbeConstruction.Inputs.finiteResidue A
      character := fun a => if ha : a = 0 then 1 else
        GlobalPairCancel.principalCharacter A σ
          (PrincipalProbeConstruction.Inputs.rowIdeal A a ha) a
          (PrincipalProbeConstruction.Inputs.rowIdeal_generates A a ha)
      additiveCharacter := e
      gammaTwo := fun q => A.idealGauss σ hS q.val (r q.val) (hr q.val) 2
      theta := fun _ => 0 }
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro I
    obtain ⟨a, _, ha, hallowed⟩ := Classical.choose_spec (C.allowed_integral I)
    exact ⟨a, ha, hallowed⟩
  · intro I a ha
    change (if ha0 : a = 0 then 1 else
      GlobalPairCancel.principalCharacter A σ
        (PrincipalProbeConstruction.Inputs.rowIdeal A a ha0) a
        (PrincipalProbeConstruction.Inputs.rowIdeal_generates A a ha0)) = _
    rw [dif_neg ha.1]
    have hI := generatedIdeal_unique
      (PrincipalProbeConstruction.Inputs.rowIdeal_generates A a ha.1) ha
    cases hI
    rfl
  · intro x
    rfl
  · intro q
    rfl

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

def branchIntegrand (P : PoolPresentation family) (i : Fin family.count)
    (key : Unit ⊕ (P.pool.primes × AmplifierValuation)) (ξ : ℝ) : ℝ :=
  (physical P ⟨i, key⟩).outerWeight *
    (physical P ⟨i, key⟩).source.phaseEnergy (hDiff := Arithmetic.different c)
      (physical P ⟨i, key⟩).firstPoint ξ

theorem physical_kernel (P : PoolPresentation family) (i : Fin family.count)
    (key : Unit ⊕ (P.pool.primes × AmplifierValuation)) :
    (physical P ⟨i, key⟩).firstKernel = (family.source i).firstKernel := by
  cases key <;> rfl

theorem branch_integrable (P : PoolPresentation family) (i : Fin family.count)
    (key : Unit ⊕ (P.pool.primes × AmplifierValuation)) :
    Integrable (branchIntegrand P i key)
      (actualFourierMeasure (family.source i).firstKernel) := by
  exact ((physical P ⟨i, key⟩).source.phaseEnergy_integrable
    (hDiff := Arithmetic.different c) (family.source i).firstKernel
    (physical P ⟨i, key⟩).firstPoint).const_mul _

theorem branch_integral (P : PoolPresentation family) (i : Fin family.count)
    (key : Unit ⊕ (P.pool.primes × AmplifierValuation)) :
    (∫ ξ, branchIntegrand P i key ξ
      ∂actualFourierMeasure (family.source i).firstKernel) =
        (physical P ⟨i, key⟩).cost := by
  rw [branchIntegrand, integral_const_mul]
  unfold PhysicalSource.cost
  rw [physical_kernel]

theorem pointwise_energy (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (ξ : ℝ) :
    (family.source i).outerWeight *
      (family.source i).source.phaseEnergy (hDiff := Arithmetic.different c)
        (family.source i).firstPoint ξ ≤
      ∑ key, branchIntegrand P i key ξ := by
  obtain ⟨D, hD⟩ := exists_coefficient_recipes (Arithmetic.context c)
  let coeff := FirstGaussPoolData.twistedCoefficient
    (family.source i).source.coefficient (family.source i).firstPoint ξ
  have hb := (P.data i).energy_bound (Arithmetic.different c) coeff
  change ((P.data i).directSource coeff).energy (Arithmetic.different c) ≤ _ at hb
  dsimp only [coeff] at hb
  rw [(P.data i).directSource_twisted] at hb
  change ((P.data i).directSource (family.source i).source.coefficient).phaseEnergy
    (hDiff := Arithmetic.different c) (family.source i).firstPoint ξ ≤ _ at hb
  rw [hP.original i] at hb
  apply (mul_le_mul_of_nonneg_left hb (family.source i).outerWeight_nonneg).trans_eq
  rw [(P.data i).energy_eq_sources (Arithmetic.different c) D hD]
  simp_rw [(P.data i).mainSource_twisted, (P.data i).residualSource_twisted]
  rw [sum_branch]
  simp only [branchIntegrand, physical, main, error, AmplifierValuation.multiplicity,
    ActualGaussSource.phaseEnergy, Finset.sum_add_distrib, mul_add, Finset.mul_sum,
    mul_assoc]

theorem source_cost_le_branches (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) :
    (family.source i).cost ≤ ∑ key, (physical P ⟨i, key⟩).cost := by
  calc
    (family.source i).cost =
        ∫ ξ, (family.source i).outerWeight *
          (family.source i).source.phaseEnergy (hDiff := Arithmetic.different c)
            (family.source i).firstPoint ξ
          ∂actualFourierMeasure (family.source i).firstKernel := by
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ ξ, ∑ key, branchIntegrand P i key ξ
        ∂actualFourierMeasure (family.source i).firstKernel := by
      apply integral_mono
        (((family.source i).source.phaseEnergy_integrable
          (hDiff := Arithmetic.different c) (family.source i).firstKernel
            (family.source i).firstPoint).const_mul _)
        (integrable_finsetSum _ (fun key _ => branch_integrable P i key))
      exact pointwise_energy P hP i
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun key _ => branch_integrable P i key)]
      exact Finset.sum_congr rfl (fun key _ => branch_integral P i key)

theorem family_cost_le_expansion (P : PoolPresentation family) (hP : P.Realizes) :
    family.cost ≤ (expansion P).cost := by
  rw [expansion_cost]
  unfold FirstCauchyFamily.cost
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum fun i _ => source_cost_le_branches P hP i

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3
