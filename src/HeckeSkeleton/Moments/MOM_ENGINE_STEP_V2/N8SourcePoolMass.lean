module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceRawMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9FirstRowExponent

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One pool prefactor for the same first arithmetic index

The original row and frozen-divisor norm windows give one common pool
density threshold.  Every error pays its own moving prime norm using
the exact 1/6/7 factor.  Reindexing retains the original first source,
and the one pool contributes only its stated `p.loss` power.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.CenteredMomentCounting
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance n8PoolMassValuationFintype : Fintype AmplifierValuation where
  elems := {.one, .six, .seven}
  complete := by intro e; cases e <;> simp

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace AmplifierValuation

theorem movingMultiplicity_eq (e : AmplifierValuation) :
    e.movingMultiplicity = amplifierMovingExponent e.multiplicity := by
  cases e <;> rfl

theorem localPayment_le_one (e : AmplifierValuation) (q : ExteriorPrime (Arithmetic.data c)) :
    FirstGaussPoolData.localErrorWeight q e.multiplicity * Q q ^ e.movingMultiplicity ≤ 1 := by
  rw [movingMultiplicity_eq e]
  exact localErrorWeight_mul_moving_norm_le_one q e.multiplicity

end AmplifierValuation

namespace PoolPresentation

variable (pool : PoolPresentation family)

def indexPrefactor (j : pool.Index) : ℝ :=
  (4 / (pool.data j.1).density) *
    match j.2 with
    | .inl _ => (pool.data j.1).multiplicity * call.base ^ (recipeInductionSigma c / 3)
    | .inr qe => FirstGaussPoolData.localErrorWeight qe.1.val qe.2.multiplicity *
        Q qe.1.val ^ qe.2.movingMultiplicity

def prefactorMass (i : Fin family.count) : ℝ :=
  ∑ branch : Unit ⊕ (pool.pool.primes × AmplifierValuation),
    pool.indexPrefactor ⟨i, branch⟩

theorem prefactorMass_eq (i : Fin family.count) :
    pool.prefactorMass i =
      (4 / (pool.data i).density) *
        ((pool.data i).multiplicity * call.base ^ (recipeInductionSigma c / 3)) +
      ∑ q : pool.pool.primes, ∑ e : AmplifierValuation,
        (4 / (pool.data i).density) *
          (FirstGaussPoolData.localErrorWeight q.val e.multiplicity *
            Q q.val ^ e.movingMultiplicity) := by
  simp [prefactorMass, indexPrefactor, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem firstIndexWeight_eq (j : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin j source) :
    source.firstIndexWeight = (family.source j.1).firstIndexWeight := by
  rcases j with ⟨i, branch⟩
  cases branch with
  | inl u =>
    rcases horigin with ⟨_, _, _, _, _, _, _, hfirst⟩
    unfold PhysicalSource.firstIndexWeight
    rw [hfirst]
  | inr qe =>
    rcases horigin with
      ⟨_, _, _, _, _, _, _, hselected, hopposite, _, hdivisor, _, _, _, _, _, _, _⟩
    unfold PhysicalSource.firstIndexWeight
    rw [hselected, hopposite, hdivisor]

theorem firstIndexMass_pooled (count : ℕ) (index : Fin count ≃ pool.Index)
    (source : Fin count → PhysicalSource call p)
    (horigin : ∀ j, pool.Origin (index j) (source j)) :
    (PoolExpansion.pooled pool count index source).firstIndexMass =
      ∑ i : Fin family.count, pool.prefactorMass i * (family.source i).firstIndexWeight := by
  have he : (PoolExpansion.pooled pool count index source).firstIndexMass =
      ∑ j : pool.Index, pool.indexPrefactor j * (family.source j.1).firstIndexWeight := by
    apply Fintype.sum_equiv index _ _
    intro j
    change pool.indexPrefactor (index j) * (source j).firstIndexWeight = _
    rw [pool.firstIndexWeight_eq (index j) (source j) (horigin j)]
  rw [he]
  conv_lhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.sum_mul Finset.univ
    (fun branch : Unit ⊕ (pool.pool.primes × AmplifierValuation) =>
      pool.indexPrefactor ⟨i, branch⟩)
    (family.source i).firstIndexWeight).symm

end PoolPresentation

namespace N8Source

def poolMultiplicityBound (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  (firstRowExponent c p + 6 * (recipeInductionSigma c / 3)) /
    ((recipeInductionSigma c / 3) / 2)

theorem poolMultiplicityBound_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ poolMultiplicityBound c p := by
  have hs := (recipeInduction_budget (c := c)).1
  have hM := firstRowExponent_nonneg c p
  dsimp only [poolMultiplicityBound]
  positivity

theorem original_pool_prefactor_mass (c : TargetContext K) (p : SourceParameters c) :
    ∃ C threshold : ℝ, 0 < C ∧ 1 < threshold ∧
      ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base → threshold ≤ call.base →
      ∀ (F : FirstPresentation call p) (family : FirstCauchyFamily F),
        F.Realizes → family.Realizes → (∀ i, (family.source i).Windows) →
      ∀ pool : PoolPresentation family, pool.Realizes →
      ∀ i : Fin family.count, pool.prefactorMass i ≤ C * call.base ^ p.loss := by
  let ell : ℝ := recipeInductionSigma c / 3
  have hell : 0 < ell := div_pos (recipeInduction_budget (c := c)).1 (by norm_num)
  have hsmall : p.loss < ell := by
    dsimp only [ell]
    linarith [p.loss_small, p.loss_pos]
  obtain ⟨Z₀, hZ₀, hpool⟩ := uniform_pool_density_and_mass
    (K := K) (A := Arithmetic.data c) ell p.loss
    (firstRowExponent c p) (columnExponent c) hell p.loss_pos hsmall
    (firstRowExponent_nonneg c p) (columnExponent_pos c).le
  let E : ℝ := (Fintype.card AmplifierValuation : ℝ)
  let B : ℝ := poolMultiplicityBound c p
  have hB : 0 ≤ B := poolMultiplicityBound_nonneg c p
  have hE : 0 ≤ E := Nat.cast_nonneg _
  have hIC : 0 < idealCountConstant K :=
    zero_lt_one.trans_le (one_le_idealCountConstant K)
  refine ⟨8 * B + 8 * (E + 1) * idealCountConstant K, Z₀, by positivity,
    hZ₀, ?_⟩
  intro call input large largePool F family hF hf hwindows pool hp i
  have hbase_pos : 0 < call.base := call.base_pos
  have hM : (pool.data i).rowExponent ≤ firstRowExponent c p := by
    rw [hp.rowExponent i]
    exact family.rowExponent_le input large hF hf i (hwindows i)
  have hS : (pool.data i).frozenExponent ≤ columnExponent c := by
    rw [hp.frozenExponent i]
    exact idealLogLength_le_of_norm (call := call)
      (nonZeroDivisors.coe_ne_zero (family.source i).first.residualDivisor) _
      (family.residual_norm input large hF hf i)
  have hd := hpool call.base largePool ∅ pool.pool
    (pool.data i).rowExponent (pool.data i).frozenExponent hM hS
  have hinv : 1 / (pool.data i).density ≤ 2 * call.base ^ (-ell + p.loss) := hd.2.1
  have hcard : (pool.pool.primes.card : ℝ) / (pool.data i).density ≤
      2 * idealCountConstant K * call.base ^ p.loss := hd.2.2.1
  have hmult : (pool.data i).multiplicity ≤ B := by
    exact div_le_div_of_nonneg_right (add_le_add hM le_rfl)
      (div_nonneg hell.le (by norm_num))
  have hpref : 4 / (pool.data i).density ≤ 8 * call.base ^ (-ell + p.loss) := by
    calc
      _ = 4 * (1 / (pool.data i).density) := by ring
      _ ≤ 4 * (2 * call.base ^ (-ell + p.loss)) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = _ := by ring
  have hmain : (4 / (pool.data i).density) *
      ((pool.data i).multiplicity * call.base ^ ell) ≤
        8 * B * call.base ^ p.loss := by
    apply (mul_le_mul hpref
      (mul_le_mul_of_nonneg_right hmult (Real.rpow_nonneg call.base_pos.le _))
      (mul_nonneg (pool.data i).multiplicity_nonneg (Real.rpow_nonneg call.base_pos.le _))
      (by positivity)).trans_eq
    have he : -ell + p.loss + ell = p.loss := by ring
    rw [show (8 * call.base ^ (-ell + p.loss)) * (B * call.base ^ ell) =
      (8 * B) * (call.base ^ (-ell + p.loss) * call.base ^ ell) by ring,
      ← Real.rpow_add call.base_pos, he]
  have herr : (∑ q : pool.pool.primes, ∑ e : AmplifierValuation,
      (4 / (pool.data i).density) *
        (FirstGaussPoolData.localErrorWeight q.val e.multiplicity *
          Q q.val ^ e.movingMultiplicity)) ≤
        8 * E * idealCountConstant K * call.base ^ p.loss := by
    calc
      _ ≤ ∑ _q : pool.pool.primes, ∑ _e : AmplifierValuation,
          4 / (pool.data i).density := by
        apply Finset.sum_le_sum
        intro q _
        apply Finset.sum_le_sum
        intro e _
        have hfactor_nonneg : 0 ≤ (4 / (pool.data i).density : ℝ) :=
          div_nonneg (by norm_num) (pool.data i).density_pos.le
        exact (mul_le_mul_of_nonneg_left
          (AmplifierValuation.localPayment_le_one e q.val) hfactor_nonneg).trans_eq
            (mul_one _)
      _ = (4 * E) * ((pool.pool.primes.card : ℝ) / (pool.data i).density) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        dsimp only [E]
        ring
      _ ≤ (4 * E) * (2 * idealCountConstant K * call.base ^ p.loss) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = _ := by ring
  rw [pool.prefactorMass_eq]
  apply (add_le_add hmain herr).trans
  have hcoef : 8 * B + 8 * E * idealCountConstant K ≤
      8 * B + 8 * (E + 1) * idealCountConstant K := by nlinarith
  exact (show 8 * B * call.base ^ p.loss +
      8 * E * idealCountConstant K * call.base ^ p.loss =
      (8 * B + 8 * E * idealCountConstant K) * call.base ^ p.loss by ring).le.trans
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg call.base_pos.le _))

theorem original_expansion_index_reduction (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) :
    ∃ C threshold : ℝ, 0 < C ∧ 1 ≤ threshold ∧
      ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      threshold ≤ call.base → ∀ trace : SourceTrace call p, trace.Realizes →
      trace.expansion.firstIndexMass ≤
        C * call.base ^ p.loss * trace.cauchy.firstIndexMass := by
  obtain ⟨C, Z₀, hC, hZ₀, hmass⟩ := original_pool_prefactor_mass c p
  let C' : ℝ := max C 1
  refine ⟨C', max Z₀ (normThreshold c frame),
    zero_lt_one.trans_le (le_max_right _ _), hZ₀.le.trans (le_max_left _ _), ?_⟩
  intro call input hframe large trace htrace
  have hbase_pos : 0 < call.base := call.base_pos
  have largeNorm : normThreshold c call.frame ≤ call.base := by
    rw [hframe]
    exact (le_max_right _ _).trans large
  have largePool : Z₀ ≤ call.base := (le_max_left _ _).trans large
  have hfactor : 1 ≤ C' * call.base ^ p.loss :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (Real.one_le_rpow call.domain.scale.le p.loss_pos.le)
  cases he : trace.expansion with
  | direct =>
    change (∑ i : Fin trace.cauchy.count,
      (1 : ℝ) * (trace.cauchy.source i).firstIndexWeight) ≤
        C' * call.base ^ p.loss * trace.cauchy.firstIndexMass
    simp only [one_mul]
    exact le_mul_of_one_le_left
      (Finset.sum_nonneg (fun i _ => (trace.cauchy.source i).firstIndexWeight_nonneg)) hfactor
  | pooled pool count index source =>
    have hexp := htrace.expansion
    rw [he] at hexp
    rw [pool.firstIndexMass_pooled count index source hexp.2.2,
      FirstCauchyFamily.firstIndexMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (trace.cauchy.source i).firstIndexWeight_nonneg
    exact (hmass call input largeNorm largePool trace.first trace.cauchy
      htrace.first htrace.cauchy htrace.firstWindows pool hexp.2.1 i).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg call.base_pos.le _))

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolPresentation.firstIndexMass_pooled
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_pool_prefactor_mass
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_expansion_index_reduction
