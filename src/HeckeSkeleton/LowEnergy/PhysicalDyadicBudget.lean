import HeckeSkeleton.LowEnergy.ExponentTail
import HeckeSkeleton.LowEnergy.GaussianDyadicBudget

/-!
# Physical dual thresholds and the complete annular tail budget

The ramified excess is `v + 3*b + e - T`, so the shell threshold is `T-e`.
The low conductor ledger bounds this threshold uniformly even in remote
Gaussian annuli. No truncation of the Gaussian or dual summations occurs.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.PhysicalDyadicBudget
open HeckeSkeleton.LowEnergy.Numerics HeckeSkeleton.LowEnergy.DyadicTail
open scoped BigOperators

def annularError (Z delta C k : ℝ) : ℝ :=
  delta + (|k| + C) / Real.log Z

def dualCutoff (Z T e : ℝ) : ℕ :=
  Nat.ceil (max ((T - e) * Real.log Z / Real.log 2) 0)

theorem annularError_nonneg {Z delta C k : ℝ}
    (hZ : 1 < Z) (hdelta : 0 ≤ delta) (hC : 0 ≤ C) :
    0 ≤ annularError Z delta C k := by
  unfold annularError
  exact add_nonneg hdelta (div_nonneg (add_nonneg (abs_nonneg _) hC)
    (Real.log_pos hZ).le)

theorem dual_threshold_upper
    {d O H A N B z e ell theta T eta : ℝ}
    (hd : 0 ≤ d) (hO : 0 ≤ O) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (he : -eta ≤ e)
    (hwidth : O + H ≤ (5 / 6 : ℝ) - 2 * d + eta)
    (hconductor : 2 * A ≤ O + eta)
    (hslot : z ≤ ell + eta) (hell : ell ≤ (1 / 6 : ℝ) - d + eta)
    (htheta : |theta| ≤ eta)
    (hT : T = 2 * H + 2 * A + 2 * z - 1 - ell - theta - N - 3 * B) :
    T - e ≤ (5 / 6 : ℝ) + 8 * eta := by
  have hdual := low_dual_length_with_errors hwidth hconductor hslot hell
    (abs_le.mp htheta).1 hN hB hT
  linarith

theorem cutoff_affine {Z delta C k T e : ℝ}
    (hZ : 1 < Z) (hdelta : 0 ≤ delta) (hC : 0 ≤ C)
    (hT : T - e ≤ (5 / 6 : ℝ) + 8 * annularError Z delta C k) :
    (dualCutoff Z T e : ℝ) ≤
      (((5 / 6 : ℝ) + 8 * delta) / Real.log 2) * Real.log Z +
        (8 / Real.log 2) * |k| + 8 * C / Real.log 2 + 1 := by
  have hz : 0 < Real.log Z := Real.log_pos hZ
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hL : (T - e) * Real.log Z / Real.log 2 ≤
      (((5 / 6 : ℝ) + 8 * delta) / Real.log 2) * Real.log Z +
        (8 / Real.log 2) * |k| + 8 * C / Real.log 2 := by
    calc
      _ = (T - e) * (Real.log Z / Real.log 2) := by ring
      _ ≤ ((5 / 6 : ℝ) + 8 * annularError Z delta C k) *
          (Real.log Z / Real.log 2) := mul_le_mul_of_nonneg_right hT (div_pos hz htwo).le
      _ = _ := by
        unfold annularError
        field_simp [hz.ne', htwo.ne']
        <;> ring
  exact ceiling_cutoff_affine hZ.le (by positivity) (by positivity) (by positivity) hL

theorem dual_penalty_le_weight {Z T e : ℝ} (hZ : 1 < Z) (i : ℕ × ℕ) :
    Z ^ (-max (((i.1 : ℝ) + 3 * i.2) * Real.log 2 / Real.log Z - (T - e)) 0) ≤
      weight (dualCutoff Z T e) i := by
  have hc : (T - e) * Real.log Z / Real.log 2 ≤ (dualCutoff Z T e : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  simpa only [one_mul, neg_one_mul] using
    real_width_penalty_le_weight hZ (le_refl (1 : ℝ)) (dualCutoff Z T e) hc i

theorem annular_error_power {Z : ℝ} (hZ : 1 < Z) (delta C k : ℝ) :
    Z ^ (2 * delta + 21 * annularError Z delta C k) =
      Z ^ (23 * delta) * Real.exp (21 * (|k| + C)) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  rw [annularError, log_error_power_identity hZ]
  rw [← mul_assoc, ← Real.rpow_add (zero_lt_one.trans hZ)]
  congr 2
  ring

theorem annular_error_half_power {Z : ℝ} (hZ : 1 < Z) (delta C k : ℝ) :
    Z ^ (delta + (21 / 2 : ℝ) * annularError Z delta C k) =
      Z ^ ((23 / 2 : ℝ) * delta) * Real.exp ((21 / 2 : ℝ) * (|k| + C)) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  rw [annularError, log_error_power_identity hZ]
  rw [← mul_assoc, ← Real.rpow_add (zero_lt_one.trans hZ)]
  congr 2
  ring

/-- The actual normalized Gaussian seminorm, the physical excess dual
length, and every annulus are summed in one theorem. The only length input
is the explicit low arithmetic inequality proved above. -/
theorem all_physical_annuli_and_dual_dyads
    (J : ℕ) (A0 E delta C eps : ℝ)
    (hdelta : 0 ≤ delta) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (Z : ℝ), 1 < Z → ∀ (T e : ℤ → ℝ),
      (∀ k : ℤ, T k - e k ≤ (5 / 6 : ℝ) +
        8 * annularError Z delta C (k : ℝ)) →
      Summable (fun i : ℤ × (ℕ × ℕ) =>
        Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 *
          Z ^ (-max (((i.2.1 : ℝ) + 3 * i.2.2) * Real.log 2 / Real.log Z -
            (T i.1 - e i.1)) 0)) ∧
      (∑' i : ℤ × (ℕ × ℕ),
        Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 *
          Z ^ (-max (((i.2.1 : ℝ) + 3 * i.2.2) * Real.log 2 / Real.log Z -
            (T i.1 - e i.1)) 0)) ≤ D * Z ^ eps := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨D, hD, hbudget⟩ := GaussianDyadicBudget.all_annuli_all_dyads
    J A0 E (((5 / 6 : ℝ) + 8 * delta) / Real.log 2)
    (8 / Real.log 2) (8 * C / Real.log 2 + 1) eps
    (by positivity) (by positivity) (by positivity) heps
  refine ⟨D, hD, ?_⟩
  intro Z hZ T e hT
  let M : ℤ → ℕ := fun k => dualCutoff Z (T k) (e k)
  have hm : ∀ k : ℤ, (M k : ℝ) ≤
      (((5 / 6 : ℝ) + 8 * delta) / Real.log 2) * Real.log Z +
      (8 / Real.log 2) * |(k : ℝ)| + (8 * C / Real.log 2 + 1) := by
    intro k
    simpa only [M, add_assoc] using cutoff_affine hZ hdelta hC (hT k)
  obtain ⟨hs, hb⟩ := hbudget Z hZ.le M hm
  let f : ℤ × (ℕ × ℕ) → ℝ := fun i =>
    Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 *
      Z ^ (-max (((i.2.1 : ℝ) + 3 * i.2.2) * Real.log 2 / Real.log Z -
        (T i.1 - e i.1)) 0)
  have hf0 : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (GaussianSeminorm.seminorm_nonneg _ _ _))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hle (i : ℤ × (ℕ × ℕ)) : f i ≤
      Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 * weight (M i.1) i.2 :=
    mul_le_mul_of_nonneg_left (dual_penalty_le_weight hZ i.2)
      (mul_nonneg (Real.exp_pos _).le (GaussianSeminorm.seminorm_nonneg _ _ _))
  have hf : Summable f := hs.of_nonneg_of_le hf0 hle
  exact ⟨hf, (hf.tsum_le_tsum hle hs).trans hb⟩

#print axioms dual_threshold_upper
#print axioms cutoff_affine
#print axioms all_physical_annuli_and_dual_dyads

end HeckeSkeleton.LowEnergy.PhysicalDyadicBudget
