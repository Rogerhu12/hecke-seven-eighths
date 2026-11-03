import HeckeSkeleton.HighBinSupport.EulerProducts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# Euler product bounds without division by local factors

The finite exceptional factors may vanish.  They are split by multiplication
with a finitely supported family, never by dividing a regular Euler product.
The summability premise below is a scalar prime-norm majorant, not the
desired convergence or global estimate.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open Filter
open scoped BigOperators Topology

theorem finite_product_norm_le_exp_sum {ι : Type*} (F : Finset ι)
    (f : ι → ℂ) (b : ι → ℝ) (hb : ∀ i ∈ F, 0 ≤ b i)
    (hf : ∀ i ∈ F, ‖f i - 1‖ ≤ b i) :
    ‖∏ i ∈ F, f i‖ ≤ Real.exp (∑ i ∈ F, b i) := by
  have hnorm (i : ι) (hi : i ∈ F) : ‖f i‖ ≤ 1 + b i := by
    have h := norm_add_le (f i - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith [hf i hi]
  calc
    ‖∏ i ∈ F, f i‖ = ∏ i ∈ F, ‖f i‖ := norm_prod _ _
    _ ≤ ∏ i ∈ F, (1 + b i) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hnorm
    _ ≤ ∏ i ∈ F, Real.exp (b i) := Finset.prod_le_prod₀
      (fun i hi => by linarith [hb i hi])
      (fun i _ => by linarith [Real.add_one_le_exp (b i)])
    _ = Real.exp (∑ i ∈ F, b i) := (Real.exp_sum _ _).symm

theorem product_norm_le_exp_tsum {ι : Type*} (f : ι → ℂ) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hsum : Summable b)
    (hf : ∀ i, ‖f i - 1‖ ≤ b i) :
    Multipliable f ∧ ‖∏' i, f i‖ ≤ Real.exp (∑' i, b i) := by
  have hs : Summable (fun i => ‖f i - 1‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hf
  have hm : Multipliable f := by
    have he (i : ι) : 1 + (f i - 1) = f i := by ring
    simpa only [he] using multipliable_one_add_of_summable hs
  refine ⟨hm, ?_⟩
  apply le_of_tendsto (hm.hasProd.norm)
  exact Filter.Eventually.of_forall fun F => by
    simpa only [norm_prod] using
      (finite_product_norm_le_exp_sum F f b (fun i _ => hb i) (fun i _ => hf i)).trans
        (Real.exp_le_exp.mpr (hsum.sum_le_tsum F (fun i _ => hb i)))

/-- Arbitrary finitely many replacements preserve convergence and have an
explicit product bound even when a replaced or unreplaced factor is zero. -/
theorem finite_exceptional_product_bound {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (f : ι → ℂ) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hsum : Summable b)
    (hf : ∀ i, i ∉ E → ‖f i - 1‖ ≤ b i) :
    Multipliable f ∧
      ‖∏' i, f i‖ ≤ (∏ i ∈ E, ‖f i‖) * Real.exp (∑' i, b i) := by
  let g : ι → ℂ := fun i => if i ∈ E then f i else 1
  let h : ι → ℂ := fun i => if i ∈ E then 1 else f i
  have hh : ∀ i, ‖h i - 1‖ ≤ b i := by
    intro i
    by_cases hi : i ∈ E
    · simpa [h, hi] using hb i
    · simpa [h, hi] using hf i hi
  obtain ⟨hhM, hhB⟩ := product_norm_le_exp_tsum h b hb hsum hh
  have hg : HasProd g (∏ i ∈ E, f i) := by
    have hg' := hasProd_prod_of_ne_finset_one (s := E) (f := g)
      (L := SummationFilter.unconditional ι) (fun i hi => by simp [g, hi])
    simpa only [g, Finset.prod_ite_mem, Finset.inter_self] using hg'
  have heq : (fun i => g i * h i) = f := by
    funext i
    by_cases hi : i ∈ E <;> simp [g, h, hi]
  have hp := hg.mul hhM.hasProd
  rw [heq] at hp
  refine ⟨hp.multipliable, ?_⟩
  rw [hp.tprod_eq, norm_mul, norm_prod]
  exact mul_le_mul_of_nonneg_left hhB (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

/-- The regular product has a single bound independent of every height
and of the point in the whole swept tube. -/
theorem phaseRowEuler_tprod_uniform_bound {ι : Type*} (q : ι → ℝ)
    (cW cD cE : ι → ℂ) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e)))
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖∏' i, phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2‖ ≤
      Real.exp (∑' i, (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e)) := by
  exact (product_norm_le_exp_tsum _ _
    (fun i => mul_nonneg (div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le)
      (Real.rpow_nonneg (by linarith [hq i]) _))
    (hsum.mul_left _) (fun i => phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
      (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv)).2

#print axioms finite_exceptional_product_bound
#print axioms phaseRowEuler_tprod_uniform_bound

/-- A fixed finite set of small primes contributes only a constant.  For
the remaining primes, a pointwise bound by 10 is absorbed by any prescribed
positive norm power after its explicit cutoff. -/
theorem finite_exceptional_subpower {ι : Type*} [DecidableEq ι]
    (E small : Finset ι) (f : ι → ℂ) (q : ι → ℝ) (N η : ℝ)
    (hη : 0 ≤ η) (hq : ∀ i ∈ E, 1 ≤ q i)
    (hprod : (∏ i ∈ E, q i) ≤ N)
    (hf : ∀ i ∈ E, ‖f i‖ ≤ 10)
    (hlarge : ∀ i ∈ E, i ∉ small → 10 ≤ (q i) ^ η) :
    (∏ i ∈ E, ‖f i‖) ≤ (10 : ℝ) ^ small.card * N ^ η := by
  let L := E.filter (fun i => i ∈ small)
  have hL : L ⊆ small := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hlocal (i : ι) (hi : i ∈ E) :
      ‖f i‖ ≤ (if i ∈ small then (10 : ℝ) else 1) * (q i) ^ η := by
    by_cases hs : i ∈ small
    · rw [if_pos hs]
      exact (hf i hi).trans (by nlinarith [Real.one_le_rpow (hq i hi) hη])
    · simpa [hs] using (hf i hi).trans (hlarge i hi hs)
  have hc : (∏ i ∈ E, if i ∈ small then (10 : ℝ) else 1) = 10 ^ L.card := by
    rw [Finset.prod_ite]
    simp [L]
  have hpow : (10 : ℝ) ^ L.card ≤ 10 ^ small.card :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hL)
  have hq0 : ∀ i ∈ E, 0 ≤ q i := fun i hi => (hq i hi).trans' zero_le_one
  calc
    (∏ i ∈ E, ‖f i‖) ≤
        ∏ i ∈ E, (if i ∈ small then (10 : ℝ) else 1) * (q i) ^ η :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hlocal
    _ = 10 ^ L.card * (∏ i ∈ E, q i) ^ η := by
      rw [Finset.prod_mul_distrib, hc, Real.finsetProd_rpow E q hq0 η]
    _ ≤ 10 ^ small.card * N ^ η :=
      mul_le_mul hpow (Real.rpow_le_rpow (Finset.prod_nonneg hq0) hprod hη)
        (Real.rpow_nonneg (Finset.prod_nonneg hq0) _) (by positivity)

#print axioms finite_exceptional_subpower
end HeckeSkeleton.HighBinContinuation
