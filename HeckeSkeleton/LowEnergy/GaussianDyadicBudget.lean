import HeckeSkeleton.LowEnergy.DyadicTail
import HeckeSkeleton.LowEnergy.GaussianSeminorm

/-!
# One proved budget for all Gaussian annuli and all dual dyads

The majorant contains the actual Euler seminorm of the explicit Gaussian
annulus. No summability of that seminorm is assumed. The cutoffs may vary
with the annulus through an affine `log Z, |k|` bound. Both the Gaussian and
dual tails are included in a single genuinely summable product-index series.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GaussianDyadicBudget
open HeckeSkeleton.LowEnergy.DyadicTail
open scoped BigOperators

/-- Complete scalar budget; its constant precedes Z and the dyadic cutoffs. -/
theorem all_annuli_all_dyads
    (J : ℕ) (A0 E A B C eps : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ (M : ℤ → ℕ),
      (∀ k : ℤ, (M k : ℝ) ≤ A * Real.log Z + B * |(k : ℝ)| + C) →
      Summable (fun i : ℤ × (ℕ × ℕ) =>
        Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 *
          weight (M i.1) i.2) ∧
      (∑' i : ℤ × (ℕ × ℕ),
        Real.exp (E * |(i.1 : ℝ)|) * GaussianSeminorm.seminorm i.1 J A0 *
          weight (M i.1) i.2) ≤ D * Z ^ eps := by
  let G : ℤ → ℝ := fun k =>
    Real.exp ((E + 2) * |(k : ℝ)|) * GaussianSeminorm.seminorm k J A0
  have hG0 : ∀ k, 0 ≤ G k := fun k =>
    mul_nonneg (Real.exp_pos _).le (GaussianSeminorm.seminorm_nonneg k J A0)
  have hG : Summable G := GaussianSeminorm.summable_exp_mul_seminorm J A0 (E + 2)
  let C0 : ℝ := (A + B + C + 2) ^ 2 * (1 + 2 / eps) ^ 2
  have hC0 : 0 ≤ C0 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  let D : ℝ := 1 + C0 * ∑' k, G k
  have hD : 1 ≤ D := by
    have hp : 0 ≤ C0 * ∑' k, G k := mul_nonneg hC0 (tsum_nonneg hG0)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro Z hZ M hM
  let a : ℤ → ℝ := fun k =>
    Real.exp (E * |(k : ℝ)|) * GaussianSeminorm.seminorm k J A0
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (Real.exp_pos _).le (GaussianSeminorm.seminorm_nonneg k J A0)
  let f : ℤ × (ℕ × ℕ) → ℝ := fun i => a i.1 * weight (M i.1) i.2
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (ha i.1) (by unfold weight; positivity)
  have hfiber : ∀ k, Summable (fun i : ℕ × ℕ => f (k, i)) := by
    intro k
    exact (summable_weight_and_tsum_le (M k)).1.mul_left (a k)
  have hmass (k : ℤ) : (∑' i : ℕ × ℕ, f (k, i)) ≤ (C0 * Z ^ eps) * G k := by
    change (∑' i : ℕ × ℕ, a k * weight (M k) i) ≤ _
    rw [tsum_mul_left]
    calc
      _ ≤ a k * ((M k : ℝ) + 2) ^ 2 := mul_le_mul_of_nonneg_left
        (summable_weight_and_tsum_le (M k)).2 (ha k)
      _ ≤ a k * ((A + B + C + 2) ^ 2 * (1 + 2 / eps) ^ 2 * Z ^ eps *
          Real.exp (2 * |(k : ℝ)|)) := mul_le_mul_of_nonneg_left
        (affine_cutoff_square_bound (M k) hZ heps hA hB hC (hM k)) (ha k)
      _ = _ := by
        dsimp [a, G, C0]
        rw [add_mul, Real.exp_add]
        ring
  have hmajorant : Summable (fun k => (C0 * Z ^ eps) * G k) := hG.mul_left _
  have houter : Summable (fun k : ℤ => ∑' i : ℕ × ℕ, f (k, i)) :=
    hmajorant.of_nonneg_of_le (fun k => tsum_nonneg (fun i => hf0 (k, i))) hmass
  have hf : Summable f := (summable_prod_of_nonneg hf0).mpr ⟨hfiber, houter⟩
  refine ⟨hf, ?_⟩
  change (∑' i, f i) ≤ D * Z ^ eps
  rw [hf.tsum_prod]
  calc
    _ ≤ ∑' k, (C0 * Z ^ eps) * G k := houter.tsum_le_tsum hmass hmajorant
    _ = (C0 * ∑' k, G k) * Z ^ eps := by rw [tsum_mul_left]; ring
    _ ≤ D * Z ^ eps := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)

#print axioms all_annuli_all_dyads

end HeckeSkeleton.LowEnergy.GaussianDyadicBudget
