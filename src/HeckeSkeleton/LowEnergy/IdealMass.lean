import HeckeSkeleton.LowEnergy.IdealMajorant
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual ideal harmonic and normalized column masses

These estimates apply to ideals of the ring of integers of an arbitrary
number field. No ideal-counting or harmonic-mass theorem is an input. The
required Dirichlet majorant is proved from Mathlib's number-field counting
asymptotic in `IdealMajorant`.

The final theorem controls the complete `D,P` column mass with inverse norm
normalization. Its constant is selected before all cutoffs and finite sets.
-/

namespace HeckeSkeleton.LowEnergy

open NumberField Ideal
open scoped BigOperators NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Positive absolute norm for a nonzero integral ideal. -/
theorem ideal_norm_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

/-- The integral norm is at least one. -/
theorem one_le_ideal_norm (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem ideal_summable_small_power (delta : ℝ) (hdelta : 0 < delta) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-1 - delta)) := by
  convert summable_ideal_norm_rpow K (σ := 1 + delta) (by linarith) using 1
  funext I
  congr 1
  ring

/-- A uniform small-power bound for every finite set of nonzero ideals. -/
theorem ideal_harmonic_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ s : Finset (Ideal (𝓞 K)), (∀ I ∈ s, I ≠ ⊥) →
        (∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ X) →
        (∑ I ∈ s, 1 / (Ideal.absNorm I : ℝ)) ≤ C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := reciprocal_sum_small_power
    (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
    (fun _ => Nat.cast_nonneg _) (ideal_summable_small_power K) eps heps
  refine ⟨C, hC, ?_⟩
  intro X hX s hne hcut
  exact hb X hX s (fun I hI => ideal_norm_pos K I (hne I hI)) hcut

/-- The same constant works for every injective presentation of the ideals.
This covers `ExteriorIdeal` via its underlying-ideal map, with no algebra
instance on that subtype required. -/
theorem ideal_harmonic_small_power_pullback (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι : Type*} (f : ι → Ideal (𝓞 K)),
      Function.Injective f → ∀ X : ℝ, 1 ≤ X →
      ∀ s : Finset ι, (∀ i ∈ s, f i ≠ ⊥) →
        (∀ i ∈ s, (Ideal.absNorm (f i) : ℝ) ≤ X) →
        (∑ i ∈ s, 1 / (Ideal.absNorm (f i) : ℝ)) ≤ C * X ^ eps := by
  classical
  obtain ⟨C, hC, hb⟩ := ideal_harmonic_small_power K eps heps
  refine ⟨C, hC, ?_⟩
  intro ι f hf X hX s hne hcut
  have himage :
      (∑ I ∈ s.image f, 1 / (Ideal.absNorm I : ℝ)) =
        ∑ i ∈ s, 1 / (Ideal.absNorm (f i) : ℝ) := by
    apply Finset.sum_image
    intro i _ j _ h
    exact hf h
  rw [← himage]
  apply hb X hX (s.image f)
  · intro I hI
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hI
    exact hne i hi
  · intro I hI
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hI
    exact hcut i hi

/-- A bounded number of actual ideal harmonic masses, allowing repetitions,
has one arbitrary small-power bound. In the global weighted hybrid proof
one may use the six masses `t,t,c,h,D,r`. -/
theorem ideal_harmonic_products_small_power
    (rmax : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*} [Fintype σ],
      Fintype.card σ ≤ rmax → ∀ X : ℝ, 1 ≤ X →
      ∀ sets : σ → Finset (Ideal (𝓞 K)),
      (∀ j I, I ∈ sets j → I ≠ ⊥) →
      (∀ j I, I ∈ sets j → (Ideal.absNorm I : ℝ) ≤ X) →
      (∏ j, ∑ I ∈ sets j, 1 / (Ideal.absNorm I : ℝ)) ≤ C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := bounded_harmonic_product_small_power
    (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
    (fun _ => Nat.cast_nonneg _) (ideal_summable_small_power K) rmax eps heps
  refine ⟨C, hC, ?_⟩
  intro σ _ hcard X hX sets hne hcut
  exact hb hcard X hX sets (fun j I hI => ideal_norm_pos K I (hne j I hI)) hcut

/-- Squared inactive-slot Minkowski costs have a uniform small-power bound. -/
theorem ideal_squared_harmonic_products_small_power
    (rmax : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*} [Fintype σ],
      Fintype.card σ ≤ rmax → ∀ X : ℝ, 1 ≤ X →
      ∀ sets : σ → Finset (Ideal (𝓞 K)),
      (∀ j I, I ∈ sets j → I ≠ ⊥) →
      (∀ j I, I ∈ sets j → (Ideal.absNorm I : ℝ) ≤ X) →
      (∏ j, ∑ I ∈ sets j, 1 / (Ideal.absNorm I : ℝ)) ^ 2 ≤ C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := squared_harmonic_product_small_power
    (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
    (fun _ => Nat.cast_nonneg _) (ideal_summable_small_power K) rmax eps heps
  refine ⟨C, hC, ?_⟩
  intro σ _ hcard X hX sets hne hcut
  exact hb hcard X hX sets (fun j I hI => ideal_norm_pos K I (hne j I hI)) hcut

/-- Exact square-root normalization for an actual ideal. -/
theorem normalized_ideal_coefficient_sq (I : Ideal (𝓞 K)) (z : ℂ) :
    ‖z / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)‖ ^ 2 =
      ‖z‖ ^ 2 / (Ideal.absNorm I : ℝ) := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

theorem normalized_ideal_coefficient_le (I : Ideal (𝓞 K)) (z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    ‖z / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)‖ ^ 2 ≤
      1 / (Ideal.absNorm I : ℝ) := by
  rw [normalized_ideal_coefficient_sq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz 2

/-- Normalized arbitrary coefficients have the same finite harmonic majorant. -/
theorem normalized_ideal_column_mass_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ (s : Finset (Ideal (𝓞 K))) (a : Ideal (𝓞 K) → ℂ),
      (∀ I ∈ s, I ≠ ⊥) → (∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ s, ‖a I‖ ≤ 1) →
      (∑ I ∈ s, ‖a I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)‖ ^ 2) ≤
        C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := ideal_harmonic_small_power K eps heps
  refine ⟨C, hC, ?_⟩
  intro X hX s a hne hcut ha
  exact (Finset.sum_le_sum (fun I hI =>
    normalized_ideal_coefficient_le K I (a I) (ha I hI))).trans (hb X hX s hne hcut)

/-- The complete normalized `D,P` mass can be absorbed directly into a
small power. This proof avoids a separate product-fiber divisor estimate.
The columns may vary with D and the coefficient may depend on both variables. -/
theorem factorized_ideal_column_mass_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ (ds : Finset (Ideal (𝓞 K)))
        (ps : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)))
        (a : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      (∀ D ∈ ds, D ≠ ⊥) →
      (∀ D ∈ ds, (Ideal.absNorm D : ℝ) ≤ X) →
      (∀ D ∈ ds, ∀ P ∈ ps D, P ≠ ⊥) →
      (∀ D ∈ ds, ∀ P ∈ ps D, (Ideal.absNorm P : ℝ) ≤ X) →
      (∀ D ∈ ds, ∀ P ∈ ps D, ‖a D P‖ ≤ 1) →
      (∑ D ∈ ds, (∑ P ∈ ps D,
        ‖a D P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) /
          (Ideal.absNorm D : ℝ)) ≤ C * X ^ eps := by
  obtain ⟨H, hH, hharmonic⟩ := ideal_harmonic_small_power K (eps / 2) (by positivity)
  refine ⟨H ^ 2, one_le_pow₀ hH, ?_⟩
  intro X hX ds ps a hdne hdcut hpne hpcut ha
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hcolumns (D : Ideal (𝓞 K)) (hD : D ∈ ds) :
      (∑ P ∈ ps D, ‖a D P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤
        H * X ^ (eps / 2) := by
    exact (Finset.sum_le_sum (fun P hP =>
      normalized_ideal_coefficient_le K P (a D P) (ha D hD P hP))).trans
      (hharmonic X hX (ps D) (hpne D hD) (hpcut D hD))
  calc
    _ ≤ ∑ D ∈ ds, (H * X ^ (eps / 2)) * (1 / (Ideal.absNorm D : ℝ)) := by
      apply Finset.sum_le_sum
      intro D hD
      simpa only [mul_one_div] using div_le_div_of_nonneg_right
        (hcolumns D hD) (Nat.cast_nonneg (Ideal.absNorm D))
    _ = (H * X ^ (eps / 2)) * ∑ D ∈ ds, 1 / (Ideal.absNorm D : ℝ) :=
      (Finset.mul_sum ..).symm
    _ ≤ (H * X ^ (eps / 2)) * (H * X ^ (eps / 2)) :=
      mul_le_mul_of_nonneg_left (hharmonic X hX ds hdne hdcut)
        (mul_nonneg hH0 (Real.rpow_nonneg hX0 _))
    _ = H ^ 2 * X ^ eps := by
      rw [show (H * X ^ (eps / 2)) * (H * X ^ (eps / 2)) =
        H ^ 2 * (X ^ (eps / 2)) ^ 2 by ring]
      rw [← Real.rpow_mul_natCast hX0]
      congr 1
      congr 1
      norm_num

#print axioms ideal_summable_small_power
#print axioms ideal_harmonic_small_power
#print axioms ideal_harmonic_small_power_pullback
#print axioms ideal_harmonic_products_small_power
#print axioms ideal_squared_harmonic_products_small_power
#print axioms normalized_ideal_column_mass_small_power
#print axioms factorized_ideal_column_mass_small_power

end
end HeckeSkeleton.LowEnergy
