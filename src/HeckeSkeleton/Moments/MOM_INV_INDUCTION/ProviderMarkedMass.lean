import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSourceSplit

/-! Finite positive summation and exact original overlap normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMass

open scoped Classical BigOperators

theorem energy_sum_le {ι κ : Type*} (rows : Finset ι) (I : Finset κ)
    (f : κ → ι → ℂ) :
    (∑ u ∈ rows, ‖∑ i ∈ I, f i u‖ ^ 2) ≤
      (I.card : ℝ) * ∑ i ∈ I, ∑ u ∈ rows, ‖f i u‖ ^ 2 := by
  calc
    _ ≤ ∑ u ∈ rows, (I.card : ℝ) * ∑ i ∈ I, ‖f i u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
        _root_.sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

theorem weighted_energy_le {ι : Type*} (rows : Finset ι) (w : ℂ) (hw : ‖w‖ ≤ 1)
    (f : ι → ℂ) : (∑ u ∈ rows, ‖w * f u‖ ^ 2) ≤ ∑ u ∈ rows, ‖f u‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro u hu
  rw [norm_mul, mul_pow]
  apply mul_le_of_le_one_left (sq_nonneg _)
  nlinarith [norm_nonneg w]

theorem block_sum_energy {ι κ γ : Type*} (rows : Finset ι) (Q : Finset κ) (I : Finset γ)
    (w : κ → ℂ) (f : κ → γ → ι → ℂ) (Y E : ℝ) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hw : ∀ q ∈ Q, ‖w q‖ ≤ 1)
    (hf : ∀ q ∈ Q, ∀ i ∈ I, (∑ u ∈ rows, ‖f q i u‖ ^ 2) ≤ Y * E) :
    (∑ u ∈ rows, ‖∑ q ∈ Q, w q * ∑ i ∈ I, f q i u‖ ^ 2) ≤
      (Q.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * Y * E := by
  apply (energy_sum_le rows Q (fun q u => w q * ∑ i ∈ I, f q i u)).trans
  have hq (q : κ) (hq : q ∈ Q) :
      (∑ u ∈ rows, ‖w q * ∑ i ∈ I, f q i u‖ ^ 2) ≤ (I.card : ℝ) ^ 2 * Y * E := by
    apply (weighted_energy_le rows (w q) (hw q hq) (fun u => ∑ i ∈ I, f q i u)).trans
    apply (energy_sum_le rows I (f q)).trans
    calc
      _ ≤ (I.card : ℝ) * ∑ _i ∈ I, Y * E :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => hf q hq i hi) (Nat.cast_nonneg _)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  calc
    _ ≤ (Q.card : ℝ) * ∑ _q ∈ Q, (I.card : ℝ) ^ 2 * Y * E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hq) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The extracted-prime tuple count is paid twice, by the actual
square-root normalization and the changed column scale. -/
theorem normalization_mass (Z r z G A N supportC : ℝ)
    (hZ : 0 < Z) (hN : 0 ≤ N) (hC : 0 ≤ supportC)
    (hcount : N ≤ A * Z ^ G) :
    Z ^ (-r - z) * N ^ 2 *
        (supportC * Z ^ ProviderMarkedScale.columnLength r z G) ≤ supportC * A ^ 2 := by
  have hsq := pow_le_pow_left₀ hN hcount 2
  calc
    _ ≤ Z ^ (-r - z) * (A * Z ^ G) ^ 2 *
        (supportC * Z ^ ProviderMarkedScale.columnLength r z G) := by gcongr
    _ = supportC * A ^ 2 *
        (Z ^ (-r - z) * (Z ^ G) ^ 2 * Z ^ ProviderMarkedScale.columnLength r z G) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
      have he : (-r - z) + G * (2 : ℕ) + ProviderMarkedScale.columnLength r z G = 0 := by
        unfold ProviderMarkedScale.columnLength
        norm_num
        <;> ring
      rw [he, Real.rpow_zero, mul_one]

/-- The common count may vary with the actual selected subset. Its
normalization is paid before summing over the finitely many subsets. -/
theorem selected_sum_energy {ι κ γ : Type*} {β : κ → Type*}
    (rows : Finset ι) (J : Finset κ) (Q : ∀ j, Finset (β j)) (I : Finset γ)
    (w : ∀ j, β j → ℂ) (f : ∀ j, β j → γ → ι → ℂ)
    (a M E : ℝ) (Y : κ → ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hY : ∀ j ∈ J, 0 ≤ Y j)
    (hw : ∀ j ∈ J, ∀ q ∈ Q j, ‖w j q‖ ≤ 1)
    (hmass : ∀ j ∈ J, a * ((Q j).card : ℝ) ^ 2 * Y j ≤ M)
    (hf : ∀ j ∈ J, ∀ q ∈ Q j, ∀ i ∈ I,
      (∑ u ∈ rows, ‖f j q i u‖ ^ 2) ≤ Y j * E) :
    a * (∑ u ∈ rows, ‖∑ j ∈ J, ∑ q ∈ Q j, w j q * ∑ i ∈ I, f j q i u‖ ^ 2) ≤
      (J.card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * M * E := by
  have hj (j : κ) (hj : j ∈ J) := block_sum_energy rows (Q j) I (w j) (f j)
    (Y j) E (hY j hj) hE (hw j hj) (hf j hj)
  calc
    _ ≤ a * ((J.card : ℝ) * ∑ j ∈ J,
        (∑ u ∈ rows, ‖∑ q ∈ Q j, w j q * ∑ i ∈ I, f j q i u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (energy_sum_le rows J
        (fun j u => ∑ q ∈ Q j, w j q * ∑ i ∈ I, f j q i u)) ha
    _ ≤ a * ((J.card : ℝ) * ∑ j ∈ J,
        ((Q j).card : ℝ) ^ 2 * (I.card : ℝ) ^ 2 * Y j * E) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hj) (Nat.cast_nonneg _)) ha
    _ = (J.card : ℝ) * (I.card : ℝ) ^ 2 * E *
        ∑ j ∈ J, a * ((Q j).card : ℝ) ^ 2 * Y j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (J.card : ℝ) * (I.card : ℝ) ^ 2 * E * ∑ _j ∈ J, M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmass) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMass

end
