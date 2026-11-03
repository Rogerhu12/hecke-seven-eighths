import HeckeSkeleton.LowEnergy.SmallPowers
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Actual number-field Dirichlet majorants

The ideal summability argument is adapted from the supplied
`HeckeGeneral/Analysis/IdealSummability.lean`.
The counting asymptotic is Mathlib's proved number-field theorem. In particular,
the convergence majorant is not a supplied analytic hypothesis. The finite-fiber
counting argument follows the calculation in Mathlib's DedekindZeta file.
-/

noncomputable section

namespace HeckeSkeleton.LowEnergy

open Filter Ideal NumberField Asymptotics
open scoped Topology nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The actual number of integral ideals of a given absolute norm. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

theorem idealCount_partial_sum_limit :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  unfold idealCount
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- The ordinary Dirichlet series of ideal counts converges for real part > 1. -/
theorem idealCount_lSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (idealCount K n : ℝ)) ?_ (fun n => Nat.cast_nonneg _) zero_le_one hs
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using idealCount_partial_sum_limit K)

theorem summable_idealCount_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (idealCount K n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have h := (idealCount_lSeriesSummable K (s := (σ : ℂ)) (by simpa using hσ)).norm
  convert h using 1
  funext n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · simp [hn, Real.rpow_neg, div_eq_mul_inv]

/-- The Dedekind majorant over actual integral ideals is summable.
The zero ideal contributes zero because σ > 1. -/
theorem summable_ideal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) => (absNorm I : ℝ) ^ (-σ)) := by
  classical
  have hfiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  have hsum (n : ℕ) :
      (∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, (absNorm I.val : ℝ) ^ (-σ)) =
        (idealCount K n : ℝ) * (n : ℝ) ^ (-σ) := by
    have := hfiber n
    simp_rw [show ∀ I : {I : Ideal (𝓞 K) // absNorm I = n}, absNorm I.val = n
      from fun I => I.property]
    simp [idealCount, tsum_const, nsmul_eq_mul]
  rw [summable_partition (s := fun n : ℕ => {I : Ideal (𝓞 K) | absNorm I = n})
    (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun I => ⟨absNorm I, rfl, fun _ h => h.symm⟩)]
  constructor
  · intro n
    have : Finite ↑{I : Ideal (𝓞 K) | absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    exact Summable.of_finite
  · change Summable (fun n => ∑' I : {I : Ideal (𝓞 K) // absNorm I = n},
      (absNorm I.val : ℝ) ^ (-σ))
    simp_rw [hsum]
    exact summable_idealCount_rpow K hσ

/-- Removing the zero ideal gives the majorant used by Hecke ideal series. -/
theorem summable_nonzeroIdeal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : (Ideal (𝓞 K))⁰ => (absNorm I.val : ℝ) ^ (-σ)) :=
  (summable_ideal_norm_rpow K hσ).subtype _

end HeckeSkeleton.LowEnergy
