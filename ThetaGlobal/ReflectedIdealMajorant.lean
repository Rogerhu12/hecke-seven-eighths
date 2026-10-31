import ThetaGlobal.ReflectedAbsoluteCore
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Actual ideal counting and the reflected triple majorant

The ideal-counting proof below is copied with namespace isolation from the
provided `HeckeGeneral.Analysis.IdealSummability`; the specialization at the
end is new.  This file uses only Mathlib and the newly verified generic core.

The counting asymptotic is Mathlib's proved number-field theorem. In particular,
the convergence majorant is not a supplied analytic hypothesis. The finite-fiber
counting argument follows the calculation in Mathlib's DedekindZeta file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedIdealMajorant

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


/-- The literal positive norm on nonzero integral ideals. -/
def positiveIdealNorm (I : (Ideal (𝓞 K))⁰) : ℝ := Ideal.absNorm I.val

theorem positiveIdealNorm_ge_one (I : (Ideal (𝓞 K))⁰) :
    1 ≤ positiveIdealNorm K I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.succ_le_iff.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I)

/-- The ζ_K(2) majorant, proved from Mathlib's number-field ideal counting. -/
theorem summable_positiveIdealNorm_inverseSquare :
    Summable (fun I : (Ideal (𝓞 K))⁰ =>
      ReflectedAbsolute.inverseSquare (positiveIdealNorm K I)) := by
  have hs := summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)
  apply hs.congr
  intro I
  rw [Real.rpow_neg (Nat.cast_nonneg _) 2, Real.rpow_two]
  rfl

/-- A kernel with quadratic decay gives a convergent triple sum over actual
number-field ideals, with arbitrary finite branches, masks, and unit sectors
encoded injectively.  The only supplied analytic estimate is the kernel tail.
The norm series is proved here; it is not an extra premise. -/
theorem summable_numberField_reflected_of_quadratic_tail
    {B J C : Type*} [Finite B]
    (encode : J → B × (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰)
    (hencode : Function.Injective encode)
    (sector : J → C) (scale arithmeticBound : B → ℝ)
    (hscale : ∀ b, 0 < scale b) (hbound : ∀ b, 0 ≤ arithmeticBound b)
    (coefficient : J → ℂ)
    (hcoefficient : ∀ j, ‖coefficient j‖ ≤ arithmeticBound (encode j).1)
    (kernel : C → ℝ → ℂ) (kernelBound : ℝ) (hkernelBound : 0 ≤ kernelBound)
    (hkernel : ∀ c y, 0 < y →
      ‖kernel c y‖ ≤ kernelBound * ReflectedAbsolute.inverseSquare y) :
    Summable (fun j => coefficient j * kernel (sector j)
      (scale (encode j).1 * positiveIdealNorm K (encode j).2.1 *
        positiveIdealNorm K (encode j).2.2.1 * positiveIdealNorm K (encode j).2.2.2 ^ 3)) :=
  ReflectedAbsolute.summable_reflected_of_quadratic_tail
    (positiveIdealNorm K) (positiveIdealNorm_ge_one K)
    (summable_positiveIdealNorm_inverseSquare K) encode hencode sector scale arithmeticBound
    hscale hbound coefficient hcoefficient kernel kernelBound hkernelBound hkernel

end ThetaGlobal.ReflectedIdealMajorant
