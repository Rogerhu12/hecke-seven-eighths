import HeckeSkeleton.Moments.MOM_BASE.CubeMobius
import HeckePort.Moments.Descent.DivisorSum
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

/-!
# Reopening a selected part of cube completion

After partitioning the extracted cube ideal `H`, the change of variables
`b = H * B` collects its Möbius weights in a divisor sum depending only
on `b`. The whole-index weight stays inside the original summand. In
particular this reindexing does not move any prime mark to a different
ideal, and the new coefficient is independent of the row and column.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckePort.IdealMobiusDivisorSum HeckeSkeleton.Moments.MOM_BASE

variable {K : Type} [Field K] [NumberField K]

/-- The coefficient obtained by collecting exactly the selected extracted
cube divisors. Its arguments contain no moving row or column. -/
def reopenedCubeCoefficient (P : Ideal (𝓞 K) → Prop) (b : Ideal (𝓞 K)) : ℂ :=
  ∑ H ∈ idealDivisors b, if P H then (moebius H : ℂ) else 0

theorem reopenedCubeCoefficient_norm_le (P : Ideal (𝓞 K) → Prop)
    (b : Ideal (𝓞 K)) :
    ‖reopenedCubeCoefficient P b‖ ≤ ((idealDivisors b).card : ℝ) := by
  unfold reopenedCubeCoefficient
  calc
    ‖∑ H ∈ idealDivisors b, if P H then (moebius H : ℂ) else 0‖ ≤
        ∑ H ∈ idealDivisors b, ‖if P H then (moebius H : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _H ∈ idealDivisors b, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro H _
      split_ifs
      · exact norm_ideal_moebius_le_one H
      · simp
    _ = _ := by simp

theorem reopenedCubeCoefficient_eq_zero (P : Ideal (𝓞 K) → Prop)
    (b : Ideal (𝓞 K)) (hP : ∀ H ∈ idealDivisors b, ¬ P H) :
    reopenedCubeCoefficient P b = 0 := by
  exact Finset.sum_eq_zero (fun H hH => if_neg (hP H hH))

/-- A long extracted divisor cannot contribute to a shorter reopened cube. -/
theorem longCubeCoefficient_zero_of_norm_lt (T : ℝ) (b : Ideal (𝓞 K))
    (hb : b ≠ ⊥) (hshort : (b.absNorm : ℝ) < T) :
    reopenedCubeCoefficient (fun H : Ideal (𝓞 K) => T ≤ (H.absNorm : ℝ)) b = 0 := by
  apply reopenedCubeCoefficient_eq_zero
  intro H hH hlong
  have hnorm := HeckePort.Moments.norm_le_of_dvd hb ((mem_idealDivisors hb).mp hH)
  exact (not_lt_of_ge (hlong.trans hnorm)) hshort

/-- A common scalar for a finite cube support; it is chosen before the
row, label, or live squarefree column. -/
def cubeCoefficientCap (B : Finset (Ideal (𝓞 K))) : ℝ :=
  max 1 ((B.sup (fun b => (idealDivisors b).card) : ℕ) : ℝ)

theorem cubeCoefficientCap_one_le (B : Finset (Ideal (𝓞 K))) :
    1 ≤ cubeCoefficientCap B := le_max_left _ _

theorem cubeCoefficientCap_pos (B : Finset (Ideal (𝓞 K))) :
    0 < cubeCoefficientCap B := zero_lt_one.trans_le (cubeCoefficientCap_one_le B)

theorem reopenedCubeCoefficient_le_cap (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (b : Ideal (𝓞 K)) (hb : b ∈ B) :
    ‖reopenedCubeCoefficient P b‖ ≤ cubeCoefficientCap B := by
  apply (reopenedCubeCoefficient_norm_le P b).trans
  apply le_trans _ (le_max_right _ _)
  exact_mod_cast (Finset.le_sup (f := fun b => (idealDivisors b).card) hb)

theorem cubeCoefficientCap_le (B : Finset (Ideal (𝓞 K))) (R : ℝ)
    (hR : 1 ≤ R) (hbound : ∀ b ∈ B, ((idealDivisors b).card : ℝ) ≤ R) :
    cubeCoefficientCap B ≤ R := by
  apply max_le hR
  have hsup : B.sup (fun b => (idealDivisors b).card) ≤ ⌊R⌋₊ :=
    Finset.sup_le (fun b hb => Nat.le_floor (hbound b hb))
  exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le (zero_le_one.trans hR))

/-- The single normalization scalar has the genuine ideal-divisor
small-power bound, uniformly before the cube support is chosen. -/
theorem exists_cubeCoefficientCap_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B : Finset (Ideal (𝓞 K))) (H : ℝ),
      1 ≤ H → (∀ b ∈ B, (b.absNorm : ℝ) ≤ H) →
      cubeCoefficientCap B ≤ C * H ^ ε := by
  obtain ⟨C, hC, hdiv⟩ := ideal_divisor_count_le_rpow K ε hε
  refine ⟨C, hC, ?_⟩
  intro B H hH hnorm
  apply cubeCoefficientCap_le
  · calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ C * H ^ ε := mul_le_mul hC (Real.one_le_rpow hH hε.le)
        zero_le_one (zero_le_one.trans hC)
  · intro b hb
    have h := hdiv b
    change ((idealDivisors b).card : ℝ) ≤ C * (b.absNorm : ℝ) ^ ε at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm b hb) hε.le) (zero_le_one.trans hC))

/-- The bounded coefficient passed to the one-step provider. All growth
of the divisor count is kept in the single scalar `cubeCoefficientCap`. -/
def normalizedCubeCoefficient (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (b : Ideal (𝓞 K)) : ℂ :=
  reopenedCubeCoefficient P b / (cubeCoefficientCap B : ℂ)

theorem normalizedCubeCoefficient_norm_le_one (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (b : Ideal (𝓞 K)) (hb : b ∈ B) :
    ‖normalizedCubeCoefficient P B b‖ ≤ 1 := by
  rw [normalizedCubeCoefficient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cubeCoefficientCap_pos B).le]
  exact (div_le_one (cubeCoefficientCap_pos B)).mpr (reopenedCubeCoefficient_le_cap P B b hb)

theorem cubeCoefficientCap_mul_normalized (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (b : Ideal (𝓞 K)) :
    (cubeCoefficientCap B : ℂ) * normalizedCubeCoefficient P B b =
      reopenedCubeCoefficient P b := by
  have hB : (cubeCoefficientCap B : ℂ) ≠ 0 := by
    exact_mod_cast (cubeCoefficientCap_pos B).ne'
  rw [normalizedCubeCoefficient, mul_comm, div_mul_cancel₀ _ hB]

/-- Restoring the common scalar is an exact polynomial identity. -/
theorem cube_sum_normalization (P : Ideal (𝓞 K) → Prop)
    (B : Finset (Ideal (𝓞 K))) (F : Ideal (𝓞 K) → ℂ) :
    (∑ b ∈ B, reopenedCubeCoefficient P b * F b) =
      (cubeCoefficientCap B : ℂ) * ∑ b ∈ B, normalizedCubeCoefficient P B b * F b := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, cubeCoefficientCap_mul_normalized]

/-- The normalization scalar is restored exactly twice in the positive
row energy; no label mass or divisor factor is charged again. -/
theorem cube_row_energy_normalization {ι : Type*}
    (P : Ideal (𝓞 K) → Prop) (B : Finset (Ideal (𝓞 K)))
    (rows : Finset ι) (F : ι → Ideal (𝓞 K) → ℂ) :
    (∑ k ∈ rows, ‖∑ b ∈ B, reopenedCubeCoefficient P b * F k b‖ ^ 2) =
      cubeCoefficientCap B ^ 2 *
        ∑ k ∈ rows, ‖∑ b ∈ B, normalizedCubeCoefficient P B b * F k b‖ ^ 2 := by
  simp_rw [cube_sum_normalization P B, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (cubeCoefficientCap_pos B).le, mul_pow]
  exact (Finset.mul_sum ..).symm

/-- The exact reindexing `b = H * B` for an arbitrary finite ideal
summand, with all its original zero masks and whole-index weights intact. -/
theorem selected_cube_dilates_reopen (P : Ideal (𝓞 K) → Prop)
    (F : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ)
    (hF : Function.HasFiniteSupport F) (hF0 : ∀ C, F (C, ⊥) = 0) :
    (∑' H : Ideal (𝓞 K), if P H then
      (moebius H : ℂ) * ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K), F (C, H * B)
      else 0) =
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        reopenedCubeCoefficient P CB.2 * F CB := by
  classical
  let T := hF.toFinset
  let A := cubeDivisorPool (T.image Prod.snd)
  have hT (CB : Ideal (𝓞 K) × Ideal (𝓞 K)) : CB ∈ T ↔ F CB ≠ 0 :=
    Set.Finite.mem_toFinset hF
  have houtside (H : Ideal (𝓞 K)) (hH : H ∉ A) :
      (if P H then (moebius H : ℂ) *
        ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K), F (C, H * B) else 0) = 0 := by
    have hzero (C B : Ideal (𝓞 K)) : F (C, H * B) = 0 := by
      by_contra hn
      have hHB : H * B ≠ ⊥ := by
        intro hz
        exact hn (by simpa only [hz] using hF0 C)
      exact hH (cubeDivisorPool_mem
        (Finset.mem_image_of_mem Prod.snd ((hT _).mpr hn)) hHB (dvd_mul_right H B))
    simp only [hzero, tsum_zero, mul_zero, ite_self]
  rw [tsum_eq_sum houtside]
  have hfiltered (H : Ideal (𝓞 K)) :
      Summable (fun CB : Ideal (𝓞 K) × Ideal (𝓞 K) =>
        if H ∣ CB.2 then F CB else 0) := by
    apply summable_of_hasFiniteSupport
    apply hF.subset
    intro CB hCB
    show F CB ≠ 0
    intro hzero
    exact hCB (by simp only [hzero, ite_self])
  have hterm (H : Ideal (𝓞 K)) (hH : H ∈ A) :
      (if P H then (moebius H : ℂ) *
        ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K), F (C, H * B) else 0) =
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        (if P H then (moebius H : ℂ) else 0) *
          (if H ∣ CB.2 then F CB else 0) := by
    have hH0 : H ≠ ⊥ := cubeDivisorPool_ne_zero hH
    by_cases hp : P H
    · simp only [hp, if_true]
      calc
        _ = (moebius H : ℂ) * ∑' C : Ideal (𝓞 K),
            ∑' b : Ideal (𝓞 K), if H ∣ b then F (C, b) else 0 := by
          congr 1
          apply tsum_congr
          intro C
          exact (cube_tsum_ideal_divisible H hH0 (fun b => F (C, b))).symm
        _ = _ := by rw [← (hfiltered H).tsum_prod, tsum_mul_left]
    · simp only [hp, if_false, zero_mul, tsum_zero]
  rw [Finset.sum_congr rfl hterm]
  rw [← Summable.tsum_finsetSum (fun H _ =>
    (hfiltered H).mul_left (if P H then (moebius H : ℂ) else 0))]
  apply tsum_congr
  rintro ⟨C, b⟩
  by_cases hf : F (C, b) = 0
  · simp only [hf, ite_self, mul_zero, Finset.sum_const_zero]
  have hb : b ≠ ⊥ := by
    intro hz
    exact hf (by simpa only [hz] using hF0 C)
  have hsub : idealDivisors b ⊆ A := by
    intro H hH
    exact cubeDivisorPool_mem (Finset.mem_image_of_mem Prod.snd ((hT _).mpr hf))
      hb ((mem_idealDivisors hb).mp hH)
  calc
    _ = ∑ H ∈ idealDivisors b,
        (if P H then (moebius H : ℂ) else 0) * (if H ∣ b then F (C, b) else 0) := by
      symm
      apply Finset.sum_subset hsub
      intro H _ hn
      have hnd : ¬ H ∣ b := fun hd => hn ((mem_idealDivisors hb).mpr hd)
      simp only [hnd, if_false, mul_zero]
    _ = reopenedCubeCoefficient P b * F (C, b) := by
      rw [reopenedCubeCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro H hH
      rw [if_pos ((mem_idealDivisors hb).mp hH)]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
