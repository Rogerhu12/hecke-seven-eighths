import HeckeSkeleton.LowEnergy.PhysicalDyadicBudget
import HeckeSkeleton.LowEnergy.GaussianEnergyAssembly

/-!
# Summing the physical low block majorants over every annulus and dual dyad

The raw two-sieve epsilon loss is retained until it is absorbed by the
positive-line decay.  The remaining annular exponent is paid by the actual
Gaussian seminorm.  This gives the original row Hilbert-space estimate and
both convergence assertions from the finite-block inequalities.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.PhysicalGaussianEnergy

open HeckeSkeleton.LowEnergy.PhysicalDyadicBudget
open HeckeSkeleton.LowEnergy.GaussianEnergyAssembly
open scoped BigOperators

def excess (Z T : ℝ) (i : ℕ × ℕ) : ℝ :=
  max (((i.1 : ℝ) + 3 * i.2) * Real.log 2 / Real.log Z - T) 0

theorem annular_power_factorization {Z : ℝ} (hZ : 1 < Z)
    (M delta C k T : ℝ) (i : ℕ × ℕ) :
    Z ^ (M + 2 * delta + 21 * annularError Z delta C k - 2 * excess Z T i) =
      (Real.exp ((21 / 2 : ℝ) * |k|) * Z ^ (-excess Z T i)) ^ 2 *
        (Real.exp (21 * C) * Z ^ (M + 23 * delta)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have htail : (Z ^ (-excess Z T i)) ^ 2 = Z ^ (-2 * excess Z T i) := by
    rw [← Real.rpow_mul_natCast hZ0.le]
    congr 1
    ring
  have hexp : (Real.exp ((21 / 2 : ℝ) * |k|)) ^ 2 * Real.exp (21 * C) =
      Real.exp (21 * (|k| + C)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsplit :
      Z ^ (M + 2 * delta + 21 * annularError Z delta C k - 2 * excess Z T i) =
        Z ^ M * Z ^ (2 * delta + 21 * annularError Z delta C k) *
          Z ^ (-2 * excess Z T i) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    congr 1
    ring
  rw [hsplit, annular_error_power hZ, mul_pow, htail]
  have hm : Z ^ M * Z ^ (23 * delta) = Z ^ (M + 23 * delta) :=
    (Real.rpow_add hZ0 _ _).symm
  calc
    _ = (Z ^ M * Z ^ (23 * delta)) * Real.exp (21 * (|k| + C)) *
        Z ^ (-2 * excess Z T i) := by ring
    _ = _ := by rw [hm, ← hexp]; ring

/-- The exact physical power is controlled by the square of the standard
Gaussian/dyadic amplitude.  The frozen error constant is global. -/
theorem annular_majorant_le_amplitude {Z : ℝ} (hZ : 1 < Z)
    (J : ℕ) (A0 M delta C : ℝ) (T : ℤ → ℝ) (i : Index) :
    GaussianSeminorm.seminorm i.1 J A0 ^ 2 *
        Z ^ (M + 2 * delta + 21 * annularError Z delta C (i.1 : ℝ) -
          2 * excess Z (T i.1) i.2) ≤
      amplitude J A0 (21 / 2) (fun k => dualCutoff Z (T k) 0) i ^ 2 *
        (Real.exp (21 * C) * Z ^ (M + 23 * delta)) := by
  have hp : Z ^ (-excess Z (T i.1) i.2) ≤
      DyadicTail.weight (dualCutoff Z (T i.1) 0) i.2 := by
    simpa only [excess, sub_zero] using dual_penalty_le_weight (e := 0) hZ i.2
  have hmul := mul_le_mul_of_nonneg_left hp
    (Real.exp_pos ((21 / 2 : ℝ) * |(i.1 : ℝ)|)).le
  have hsq := pow_le_pow_left₀ (by positivity :
      0 ≤ Real.exp ((21 / 2 : ℝ) * |(i.1 : ℝ)|) * Z ^ (-excess Z (T i.1) i.2)) hmul 2
  rw [annular_power_factorization hZ]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg (GaussianSeminorm.seminorm i.1 J A0)))
    (by positivity : 0 ≤ Real.exp (21 * C) * Z ^ (M + 23 * delta))
  convert h using 1 <;> (try dsimp [amplitude]) <;> ring

/-- Uniform infinite assembly of the proved physical low block bounds.
Every original row is retained; the conclusion derives convergence as
well as energy.  Constants precede the height, thresholds and row family. -/
theorem all_physical_blocks_energy (J : ℕ) (A0 delta C eps : ℝ)
    (hdelta : 0 ≤ delta) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ D : ℝ, 0 < D ∧ ∀ (Z : ℝ), 1 < Z → ∀ (T : ℤ → ℝ),
      (∀ k : ℤ, T k ≤ (5 / 6 : ℝ) + 8 * annularError Z delta C (k : ℝ)) →
      ∀ (ι : Type*) (F : Index → ι → ℂ) (M R : ℝ), 0 ≤ R →
      (∀ i, ∀ rows : Finset ι,
        (∑ r ∈ rows, ‖F i r‖ ^ 2) ≤
          GaussianSeminorm.seminorm i.1 J A0 ^ 2 *
          Z ^ (M + 2 * delta + 21 * annularError Z delta C (i.1 : ℝ) -
            2 * excess Z (T i.1) i.2) * R) →
      (∀ r, Summable (fun i => F i r)) ∧
      Summable (fun r => ‖∑' i, F i r‖ ^ 2) ∧
      (∑' r, ‖∑' i, F i r‖ ^ 2) ≤
        D * Real.exp (21 * C) * Z ^ (M + 23 * delta + 2 * eps) * R := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨D, hD, hbound⟩ := all_annuli_all_dyads_energy J A0 (21 / 2)
    (((5 / 6 : ℝ) + 8 * delta) / Real.log 2) (8 / Real.log 2)
    (8 * C / Real.log 2 + 1) eps (by positivity) (by positivity) (by positivity) heps
  refine ⟨D, hD, ?_⟩
  intro Z hZ T hT ι F M R hR hblock
  let cut : ℤ → ℕ := fun k => dualCutoff Z (T k) 0
  have hcut : ∀ k : ℤ, (cut k : ℝ) ≤
      (((5 / 6 : ℝ) + 8 * delta) / Real.log 2) * Real.log Z +
        (8 / Real.log 2) * |(k : ℝ)| + (8 * C / Real.log 2 + 1) := by
    intro k
    simpa only [cut, sub_zero, add_assoc] using
      cutoff_affine (T := T k) (e := 0) hZ hdelta hC (by simpa only [sub_zero] using hT k)
  have hr0 : 0 ≤ (Real.exp (21 * C) * Z ^ (M + 23 * delta)) * R := by positivity
  have hlocal (i : Index) (rows : Finset ι) :
      (∑ r ∈ rows, ‖F i r‖ ^ 2) ≤
        amplitude J A0 (21 / 2) cut i ^ 2 *
          ((Real.exp (21 * C) * Z ^ (M + 23 * delta)) * R) := by
    have h := mul_le_mul_of_nonneg_right
      (annular_majorant_le_amplitude hZ J A0 M delta C T i) hR
    exact (hblock i rows).trans (by simpa only [cut, mul_assoc] using h)
  obtain ⟨hpoint, hsum, he⟩ := hbound Z hZ.le cut hcut ι F
    ((Real.exp (21 * C) * Z ^ (M + 23 * delta)) * R) hr0 hlocal
  refine ⟨hpoint, hsum, he.trans_eq ?_⟩
  have hp : Z ^ (2 * eps) * Z ^ (M + 23 * delta) =
      Z ^ (M + 23 * delta + 2 * eps) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  calc
    _ = D * Real.exp (21 * C) * (Z ^ (2 * eps) * Z ^ (M + 23 * delta)) * R := by ring
    _ = _ := by rw [hp]

#print axioms annular_power_factorization
#print axioms annular_majorant_le_amplitude
#print axioms all_physical_blocks_energy

end HeckeSkeleton.LowEnergy.PhysicalGaussianEnergy
