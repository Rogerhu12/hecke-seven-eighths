import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity

/-!+# Summing actual row vectors with their annular amplitudes

The small profile amplitude is kept outside the whole linear row vector.
The result is Minkowski in the finite row Hilbert space, then a monotone
extension over all finite subsets of an arbitrary row type.  In particular,
neither pointwise series convergence nor row-energy summability is hidden in
the hypotheses: both are proved from the displayed block bounds.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.AnnularEnergy

open scoped BigOperators

theorem norm_le_amplitude_sqrt {z : ℂ} {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (h : ‖z‖ ^ 2 ≤ a ^ 2 * R) : ‖z‖ ≤ a * Real.sqrt R := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hR] using h

theorem finite_rows_minkowski {ι κ : Type*} (rows : Finset ι)
    (F : κ → ι → ℂ) (a : κ → ℝ) (R : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hR : 0 ≤ R) (hs : Summable a)
    (hblock : ∀ k, (∑ i ∈ rows, ‖F k i‖ ^ 2) ≤ (a k) ^ 2 * R) :
    (∑ i ∈ rows, ‖∑' k, F k i‖ ^ 2) ≤ (∑' k, a k) ^ 2 * R := by
  classical
  let v (k : κ) : EuclideanSpace ℂ rows := WithLp.toLp 2 (fun i => F k i)
  have hsq (k : κ) : ‖v k‖ ^ 2 = ∑ i ∈ rows, ‖F k i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : rows, ‖F k i.val‖ ^ 2) = _
    exact Finset.sum_coe_sort rows (fun i => ‖F k i‖ ^ 2)
  have hv (k : κ) : ‖v k‖ ≤ a k * Real.sqrt R := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (ha k) (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hR, hsq] using hblock k
  have hnorm : Summable (fun k => ‖v k‖) :=
    (hs.mul_right (Real.sqrt R)).of_nonneg_of_le (fun _ => norm_nonneg _) hv
  have hvsum : Summable v := hnorm.of_norm
  have heval (i : rows) : (∑' k, v k) i = ∑' k, F k i := by
    exact (EuclideanSpace.proj i).map_tsum hvsum
  have hsum : ‖∑' k, v k‖ ≤ (∑' k, a k) * Real.sqrt R := by
    calc
      _ ≤ ∑' k, ‖v k‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' k, a k * Real.sqrt R :=
        hnorm.tsum_le_tsum hv (hs.mul_right _)
      _ = _ := tsum_mul_right
  have hsum0 : 0 ≤ ∑' k, a k := tsum_nonneg ha
  have henergy := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [mul_pow, Real.sq_sqrt hR, EuclideanSpace.norm_sq_eq] at henergy
  have henergy' : (∑ i : rows, ‖∑' k, F k i.val‖ ^ 2) ≤
      (∑' k, a k) ^ 2 * R := by simpa only [heval] using henergy
  have heqsum : (∑ i : rows, ‖∑' k, F k i.val‖ ^ 2) =
      ∑ i ∈ rows, ‖∑' k, F k i‖ ^ 2 :=
    Finset.sum_coe_sort rows (fun i => ‖∑' k, F k i‖ ^ 2)
  rwa [heqsum] at henergy'

/-- The same theorem on an arbitrary row type, including all original sectors.
The hypothesis is checked only on finite row restrictions of each block. -/
theorem rows_minkowski {ι κ : Type*}
    (F : κ → ι → ℂ) (a : κ → ℝ) (R : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hR : 0 ≤ R) (hs : Summable a)
    (hblock : ∀ k, ∀ rows : Finset ι,
      (∑ i ∈ rows, ‖F k i‖ ^ 2) ≤ (a k) ^ 2 * R) :
    (∀ i, Summable (fun k => F k i)) ∧
      Summable (fun i => ‖∑' k, F k i‖ ^ 2) ∧
      (∑' i, ‖∑' k, F k i‖ ^ 2) ≤ (∑' k, a k) ^ 2 * R := by
  classical
  have hpoint (i : ι) : Summable (fun k => F k i) := by
    apply (hs.mul_right (Real.sqrt R)).of_norm_bounded
    intro k
    apply norm_le_amplitude_sqrt (ha k) hR
    simpa only [Finset.sum_singleton] using hblock k {i}
  have hfinite (rows : Finset ι) :
      (∑ i ∈ rows, ‖∑' k, F k i‖ ^ 2) ≤ (∑' k, a k) ^ 2 * R :=
    finite_rows_minkowski rows F a R ha hR hs (fun k => hblock k rows)
  exact ⟨hpoint, summable_of_sum_le (fun _ => sq_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

/-- A summable majorant can be used for all frozen labels at once. -/
theorem rows_minkowski_of_majorant {ι κ : Type*}
    (F : κ → ι → ℂ) (a b : κ → ℝ) (R : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hab : ∀ k, a k ≤ b k)
    (hR : 0 ≤ R) (hb : Summable b)
    (hblock : ∀ k, ∀ rows : Finset ι,
      (∑ i ∈ rows, ‖F k i‖ ^ 2) ≤ (a k) ^ 2 * R) :
    (∑' i, ‖∑' k, F k i‖ ^ 2) ≤ (∑' k, b k) ^ 2 * R := by
  have hs : Summable a := hb.of_nonneg_of_le ha hab
  have h := (rows_minkowski F a R ha hR hs hblock).2.2
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (tsum_nonneg ha) (hs.tsum_le_tsum hab hb) 2) hR)

/-- Tail amplitudes are removed before taking the positive row bound. -/
theorem row_energy_tail {ι κ : Type*}
    (F : κ → ι → ℂ) (a : κ → ℝ) (R : ℝ) (keep : κ → Prop)
    [DecidablePred keep] (ha : ∀ k, 0 ≤ a k) (hR : 0 ≤ R) (hs : Summable a)
    (hblock : ∀ k, ∀ rows : Finset ι,
      (∑ i ∈ rows, ‖F k i‖ ^ 2) ≤ (a k) ^ 2 * R) :
    (∑' i, ‖∑' k, if keep k then F k i else 0‖ ^ 2) ≤
      (∑' k, if keep k then a k else 0) ^ 2 * R := by
  have hnonneg (k : κ) : 0 ≤ (if keep k then a k else 0) := by
    split_ifs <;> simp [ha]
  have htail : Summable (fun k => if keep k then a k else 0) :=
    hs.of_nonneg_of_le hnonneg (fun k => by split_ifs <;> simp [ha])
  apply (rows_minkowski (fun k i => if keep k then F k i else 0)
    (fun k => if keep k then a k else 0) R
    hnonneg hR htail ?_).2.2
  intro k rows
  by_cases hk : keep k
  · simpa [hk] using hblock k rows
  · simp [hk]

#print axioms finite_rows_minkowski
#print axioms rows_minkowski
#print axioms row_energy_tail

end HeckeSkeleton.LowEnergy.AnnularEnergy
