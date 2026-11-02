import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual pool cardinality and its exact amplification factors

The prime ideal count applies to the one prescribed pool. Its index
bijection permits precisely one main term and three error valuations
for each prime. The original density lower bound controls the same
outer multiplier; no additional prime pool or eligibility assumption
is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.ThetaSkeleton.Global HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

local instance amplifierValuationFintype : Fintype AmplifierValuation where
  elems := {.one, .six, .seven}
  complete e := by cases e <;> simp

theorem amplifierValuation_card : Fintype.card AmplifierValuation = 3 := by decide

theorem localErrorWeight_le_one {A : SArithmeticData K} (q : ExteriorPrime A) (n : ℕ) :
    FirstGaussPoolData.localErrorWeight q n ≤ 1 := by
  have hQ : 1 ≤ Q q := by
    change (1 : ℝ) ≤ (Ideal.absNorm q.val.asIdeal : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun he => q.val.ne_bot (Ideal.absNorm_eq_zero_iff.mp he))
  have hp : 1 ≤ Q q ^ amplifierMovingExponent n := one_le_pow₀ hQ
  exact (le_mul_of_one_le_right (FirstGaussPoolData.localErrorWeight_nonneg q n) hp).trans
    (localErrorWeight_mul_moving_norm_le_one q n)

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem pool_card_upper (P : PoolPresentation family) :
    (P.pool.primes.card : ℝ) ≤
      idealCountConstant K * call.base ^ (recipeInductionSigma c / 3) :=
  P.pool.card_upper

theorem pool_card_one_le (P : PoolPresentation family) :
    1 ≤ (P.pool.primes.card : ℝ) := by
  have he : 0 ≤ recipeInductionSigma c / 3 - p.loss := by
    linarith [p.loss_small, p.loss_pos]
  exact (Real.one_le_rpow call.domain.scale.le he).trans P.pool.size_lower

theorem pool_density_one_le (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) : 1 ≤ (P.data i).density := by
  have he : 0 ≤ recipeInductionSigma c / 3 - 2 * p.loss := by
    linarith [p.loss_small, p.loss_pos]
  exact (Real.one_le_rpow call.domain.scale.le he).trans (hP.density i)

theorem pool_density_factor_le (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) : 4 / (P.data i).density ≤ 4 := by
  apply (div_le_iff₀ (P.data i).density_pos).mpr
  have h := pool_density_one_le P hP i
  linarith

def poolMultiplicityBound (c : TargetContext K) (degree : ℝ) : ℝ :=
  (degree + 2 * recipeInductionSigma c) / (recipeInductionSigma c / 6)

theorem poolMultiplicityBound_nonneg (c : TargetContext K) (degree : ℝ)
    (hdegree : 0 ≤ degree) : 0 ≤ poolMultiplicityBound c degree := by
  have hs := (recipeInduction_budget (c := c)).1
  unfold poolMultiplicityBound
  positivity

theorem pool_multiplicity_le (P : PoolPresentation family) (hP : P.Realizes)
    (i : Fin family.count) (degree : ℝ)
    (hrow : (family.source i).rowExponent ≤ degree) :
    (P.data i).multiplicity ≤ poolMultiplicityBound c degree := by
  have hs := (recipeInduction_budget (c := c)).1
  unfold FirstGaussPoolData.multiplicity poolMultiplicityBound
  rw [hP.rowExponent i,
    show 6 * (recipeInductionSigma c / 3) = 2 * recipeInductionSigma c by ring,
    show (recipeInductionSigma c / 3) / 2 = recipeInductionSigma c / 6 by ring]
  exact div_le_div_of_nonneg_right (add_le_add hrow le_rfl) (by positivity)

theorem pool_index_card (P : PoolPresentation family) :
    Nat.card P.Index = family.count * (1 + P.pool.primes.card * 3) := by
  simp [PoolPresentation.Index, Nat.card_eq_fintype_card, Fintype.card_sigma,
    amplifierValuation_card]

theorem pooled_count_eq (P : PoolPresentation family) (count : ℕ)
    (index : Fin count ≃ P.Index) (source : Fin count → PhysicalSource call p) :
    (PoolExpansion.pooled P count index source).count =
      family.count * (1 + P.pool.primes.card * 3) := by
  have h := Nat.card_congr index
  rw [Nat.card_fin, pool_index_card] at h
  exact h

theorem pooled_count_le (P : PoolPresentation family) (count : ℕ)
    (index : Fin count ≃ P.Index) (source : Fin count → PhysicalSource call p) :
    ((PoolExpansion.pooled P count index source).count : ℝ) ≤
      (4 * (family.count : ℝ)) * (P.pool.primes.card : ℝ) := by
  rw [pooled_count_eq]
  push_cast
  have h := mul_le_mul_of_nonneg_left (pool_card_one_le P)
    (Nat.cast_nonneg family.count : (0 : ℝ) ≤ family.count)
  nlinarith

/-- The exact index type bounds both the direct and amplified branches. -/
theorem expansion_count_le (expansion : PoolExpansion family) :
    (expansion.count : ℝ) ≤
      (4 * idealCountConstant K) * (family.count : ℝ) *
        call.base ^ (recipeInductionSigma c / 3) := by
  have hc : 1 ≤ idealCountConstant K := one_le_idealCountConstant K
  have hz : 1 ≤ call.base ^ (recipeInductionSigma c / 3) :=
    Real.one_le_rpow call.domain.scale.le
      (div_nonneg (recipeInduction_budget (c := c)).1.le (by norm_num))
  cases expansion with
  | direct =>
      have hfactor : 1 ≤ (4 * idealCountConstant K) *
          call.base ^ (recipeInductionSigma c / 3) := by
        calc
          (1 : ℝ) ≤ 4 * idealCountConstant K := by linarith
          _ ≤ _ := le_mul_of_one_le_right (by linarith) hz
      have h := le_mul_of_one_le_left (Nat.cast_nonneg family.count) hfactor
      simpa only [PoolExpansion.count, mul_assoc, mul_comm, mul_left_comm] using h
  | pooled P count index source =>
      calc
        _ ≤ (4 * (family.count : ℝ)) * (P.pool.primes.card : ℝ) :=
          pooled_count_le P count index source
        _ ≤ (4 * (family.count : ℝ)) *
            (idealCountConstant K * call.base ^ (recipeInductionSigma c / 3)) :=
          mul_le_mul_of_nonneg_left (pool_card_upper P)
            (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        _ = _ := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.localErrorWeight_le_one
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.pool_density_factor_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.expansion_count_le
