import HeckeSkeleton.LowEnergy.GaussianDyadicBudget
import HeckeSkeleton.LowEnergy.AnnularEnergy

/-!
# All annuli and all dual dyads in the original row Hilbert space

The scalar majorant is the proved Gaussian seminorm budget, not a separately
assumed summable family. Both pointwise convergence and row-energy summability
follow from finite-row block estimates. All constants precede the height,
the dual cutoffs and the row family.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GaussianEnergyAssembly
open scoped BigOperators

abbrev Index := ℤ × (ℕ × ℕ)

def amplitude (J : ℕ) (A0 E : ℝ) (M : ℤ → ℕ) (i : Index) : ℝ :=
  Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 *
    DyadicTail.weight (M i.1) i.2

theorem amplitude_nonneg (J : ℕ) (A0 E : ℝ) (M : ℤ → ℕ) (i : Index) :
    0 ≤ amplitude J A0 E M i := by
  unfold amplitude DyadicTail.weight
  positivity [GaussianSeminorm.seminorm_nonneg i.1 J A0]

/-- The actual infinite scalar budgets imply one uniform row-energy budget.
Here the finite-row inequalities are the output of MellinHybrid and the
numerical block specialization, rather than an assumption about the target. -/
theorem all_annuli_all_dyads_energy
    (J : ℕ) (A0 E A B C eps : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ D : ℝ, 0 < D ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ (M : ℤ → ℕ),
      (∀ k : ℤ, (M k : ℝ) ≤ A * Real.log Z + B * |(k : ℝ)| + C) →
      ∀ (ι : Type*) (F : Index → ι → ℂ) (R : ℝ), 0 ≤ R →
      (∀ i, ∀ rows : Finset ι,
        (∑ r ∈ rows, ‖F i r‖ ^ 2) ≤ amplitude J A0 E M i ^ 2 * R) →
      (∀ r, Summable (fun i => F i r)) ∧
      Summable (fun r => ‖∑' i, F i r‖ ^ 2) ∧
      (∑' r, ‖∑' i, F i r‖ ^ 2) ≤ D * Z ^ (2 * eps) * R := by
  obtain ⟨D, hD, hbudget⟩ := GaussianDyadicBudget.all_annuli_all_dyads
    J A0 E A B C eps hA hB hC heps
  refine ⟨D ^ 2, sq_pos_of_pos (zero_lt_one.trans_le hD), ?_⟩
  intro Z hZ M hM ι F R hR hblock
  obtain ⟨hs, hm⟩ := hbudget Z hZ M hM
  change Summable (amplitude J A0 E M) at hs
  change (∑' i, amplitude J A0 E M i) ≤ D * Z ^ eps at hm
  obtain ⟨hpoint, henergy_sum, henergy⟩ := AnnularEnergy.rows_minkowski
    F (amplitude J A0 E M) R (amplitude_nonneg J A0 E M) hR hs hblock
  refine ⟨hpoint, henergy_sum, henergy.trans ?_⟩
  have hsq := pow_le_pow_left₀
    (tsum_nonneg (amplitude_nonneg J A0 E M)) hm 2
  have hp : (D * Z ^ eps) ^ 2 = D ^ 2 * Z ^ (2 * eps) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hZ)]
    congr 2
    ring
  rw [hp] at hsq
  exact mul_le_mul_of_nonneg_right hsq hR

#print axioms all_annuli_all_dyads_energy

end HeckeSkeleton.LowEnergy.GaussianEnergyAssembly
