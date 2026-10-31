import HeckeSkeleton.LowEnergy.AnnularEnergy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Common-profile integration in the original row Hilbert space

The profile is common to all rows and all columns. Integrability is derived
from its L1 majorant and the mode energy estimate. The small scalar is kept
outside the whole linear row vector, so its square survives unchanged.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.MellinEnergy
open MeasureTheory
open scoped BigOperators

theorem finite_rows_integral_minkowski {ι : Type*} (rows : Finset ι)
    (F : ℝ → ι → ℂ) (a : ℝ → ℝ) (R : ℝ)
    (hF : ∀ i, Continuous (fun t => F t i))
    (ha : ∀ t, 0 ≤ a t) (hR : 0 ≤ R) (hint : Integrable a)
    (hblock : ∀ t, (∑ i ∈ rows, ‖F t i‖ ^ 2) ≤ a t ^ 2 * R) :
    (∑ i ∈ rows, ‖∫ t : ℝ, F t i‖ ^ 2) ≤ (∫ t : ℝ, a t) ^ 2 * R := by
  classical
  let v (t : ℝ) : EuclideanSpace ℂ rows := WithLp.toLp 2 (fun i => F t i)
  have hsq (t : ℝ) : ‖v t‖ ^ 2 = ∑ i ∈ rows, ‖F t i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : rows, ‖F t i.val‖ ^ 2) = _
    exact Finset.sum_coe_sort rows (fun i => ‖F t i‖ ^ 2)
  have hv (t : ℝ) : ‖v t‖ ≤ a t * Real.sqrt R := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (ha t) (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hR, hsq] using hblock t
  have hc : Continuous v :=
    (PiLp.continuous_toLp 2 (fun _ : rows => ℂ)).comp (continuous_pi (fun i => hF i))
  have hvi : Integrable v := (hint.mul_const (Real.sqrt R)).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall hv)
  have heval (i : rows) : (∫ t : ℝ, v t) i = ∫ t : ℝ, F t i :=
    ((EuclideanSpace.proj i).integral_comp_comm hvi).symm
  have hnorm : ‖∫ t : ℝ, v t‖ ≤ (∫ t : ℝ, a t) * Real.sqrt R := by
    calc
      _ ≤ ∫ t : ℝ, ‖v t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, a t * Real.sqrt R :=
        integral_mono hvi.norm (hint.mul_const _) hv
      _ = _ := integral_mul_const _ _
  have henergy := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow, Real.sq_sqrt hR, EuclideanSpace.norm_sq_eq] at henergy
  have henergy' : (∑ i : rows, ‖∫ t : ℝ, F t i.val‖ ^ 2) ≤
      (∫ t : ℝ, a t) ^ 2 * R := by simpa only [heval] using henergy
  have heq : (∑ i : rows, ‖∫ t : ℝ, F t i.val‖ ^ 2) =
      ∑ i ∈ rows, ‖∫ t : ℝ, F t i‖ ^ 2 :=
    Finset.sum_coe_sort rows (fun i => ‖∫ t : ℝ, F t i‖ ^ 2)
  rwa [heq] at henergy'

/-- Every mode may use arbitrary coefficients, subject to the genuine
uniform sieve estimate. The common profile is integrated only afterward. -/
theorem finite_rows_common_profile {ι : Type*} (rows : Finset ι)
    (rho : ℝ → ℂ) (F : ℝ → ι → ℂ) (R : ℝ)
    (hrho : Continuous rho) (hF : ∀ i, Continuous (fun t => F t i))
    (hint : Integrable (fun t => ‖rho t‖)) (hR : 0 ≤ R)
    (hblock : ∀ t, (∑ i ∈ rows, ‖F t i‖ ^ 2) ≤ R) :
    (∑ i ∈ rows, ‖∫ t : ℝ, rho t * F t i‖ ^ 2) ≤
      (∫ t : ℝ, ‖rho t‖) ^ 2 * R := by
  apply finite_rows_integral_minkowski rows (fun t i => rho t * F t i)
    (fun t => ‖rho t‖) R (fun i => hrho.mul (hF i)) (fun _ => norm_nonneg _) hR hint
  intro t
  simp_rw [norm_mul, mul_pow]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hblock t) (sq_nonneg _)

/-- The small kernel scalar is extracted before the mode bound and before
any positive enlargement of row or coefficient supports. -/
theorem finite_rows_common_profile_scalar {ι : Type*} (rows : Finset ι)
    (s : ℝ) (rho : ℝ → ℂ) (F : ℝ → ι → ℂ) (R : ℝ)
    (hrho : Continuous rho) (hF : ∀ i, Continuous (fun t => F t i))
    (hint : Integrable (fun t => ‖rho t‖)) (hR : 0 ≤ R)
    (hblock : ∀ t, (∑ i ∈ rows, ‖F t i‖ ^ 2) ≤ R) :
    (∑ i ∈ rows, ‖(s : ℂ) * ∫ t : ℝ, rho t * F t i‖ ^ 2) ≤
      s ^ 2 * (∫ t : ℝ, ‖rho t‖) ^ 2 * R := by
  simp_rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left
    (finite_rows_common_profile rows rho F R hrho hF hint hR hblock) (sq_nonneg s)
  simpa only [mul_assoc] using h

/-- Integrability of each literal finite separated term follows from a
common L1 density and the mode-factor bound. -/
theorem integrable_profile_mul (rho f : ℝ → ℂ) (C : ℝ)
    (hrho : Continuous rho) (hf : Continuous f)
    (hint : Integrable (fun t => ‖rho t‖))
    (hbound : ∀ t, ‖f t‖ ≤ C) : Integrable (fun t => rho t * f t) := by
  apply (hint.mul_const C).mono' (hrho.mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  change ‖rho t * f t‖ ≤ ‖rho t‖ * C
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

/-- Finite marked and column sums commute with the same actual integral,
with integrability proved rather than hidden in a formal integral identity. -/
theorem finite_sum_profile_integral {ι : Type*} (s : Finset ι)
    (rho : ℝ → ℂ) (f : ι → ℝ → ℂ) (C : ι → ℝ)
    (hrho : Continuous rho) (hf : ∀ i ∈ s, Continuous (f i))
    (hint : Integrable (fun t => ‖rho t‖))
    (hbound : ∀ i ∈ s, ∀ t, ‖f i t‖ ≤ C i) :
    (∑ i ∈ s, ∫ t : ℝ, rho t * f i t) =
      ∫ t : ℝ, rho t * ∑ i ∈ s, f i t := by
  rw [← integral_finsetSum s (fun i hi =>
    integrable_profile_mul rho (f i) (C i) hrho (hf i hi) hint (hbound i hi))]
  congr 1
  funext t
  exact (Finset.mul_sum s (f := fun i => f i t) (rho t)).symm

#print axioms finite_rows_integral_minkowski
#print axioms finite_rows_common_profile_scalar
#print axioms finite_sum_profile_integral

end HeckeSkeleton.LowEnergy.MellinEnergy
