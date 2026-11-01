import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RankinLabels

/-!
# Uniform harmonic mass of actual common-support labels

The sum is first grouped by its genuine radical.  Exact ideal counting
controls each fiber, including the subset of common primes assigned to a
child.  The inverse-norm sum of the actual radical quotients then supplies
the old-mask density.  There is no hypothesis asserting a label-mass bound.

This proves the radical weight bound, which also dominates the paired
weight `1 / sqrt (N(I) N(J))`.  Constants precede the scale, old mask and
finite label family.  The argument generalizes the harmonic-mass lemmas in
openai/math using the repository's existing number-field inverse-norm sum.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

/-- The actual radical-fiber sum retains its inverse old-mask norm. -/
theorem common_radical_harmonic_mass_dyadic (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Ideal (𝓞 K)), Squarefree s → s ≠ 0 →
      ∀ S : Finset (Label K), (∀ v ∈ S, Valid s v) → ∀ Y : ℝ, 0 < Y →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ Y ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Y) →
      (∑ v ∈ S, 1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) ≤
        C * Y ^ (3 * e) * (columnDyadicLength Y + 1 : ℝ) / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, hC, hfiber⟩ := common_radical_fiber_count (K := K) e e he he
  have hKC : 0 < idealCountConstant K := zero_lt_one.trans_le (one_le_idealCountConstant K)
  refine ⟨C * (2 * idealCountConstant K), mul_pos hC (mul_pos (by norm_num) hKC), ?_⟩
  intro s hs hs0 S hS Y hY hN
  let rad : Label K → Ideal (𝓞 K) := fun v => commonRadical v.1.1 v.1.2
  have hRN (R : Ideal (𝓞 K)) (hR : R ∈ S.image rad) : (Ideal.absNorm R : ℝ) ≤ Y := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hR
    exact (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      ((min_le_left _ _).trans (hN v hv).1)
  have hR0 (R : Ideal (𝓞 K)) (hR : R ∈ S.image rad) : R ≠ 0 := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hR
    exact commonRadical_ne_zero _ _
  have hdiv (R : Ideal (𝓞 K)) (hR : R ∈ S.image rad) : s ∣ R := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hR
    exact old_mask_dvd_commonRadical _ _ _ hs (hS v hv).1 (hS v hv).2.1
      (hS v hv).2.2.2.1 (hS v hv).2.2.2.2.1
  have hcard (R : Ideal (𝓞 K)) (hR : R ∈ S.image rad) :
      ((S.filter (fun v => rad v = R)).card : ℝ) ≤ C * Y ^ (3 * e) := by
    calc
      _ ≤ C * Y ^ e * Y ^ e * (Ideal.absNorm R : ℝ) ^ e :=
        hfiber s S hS R (hR0 R hR) Y Y hY hY hN
      _ ≤ C * Y ^ e * Y ^ e * Y ^ e :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hRN R hR) he.le) (by positivity)
      _ = _ := by
        rw [show 3 * e = e + e + e by ring, Real.rpow_add hY, Real.rpow_add hY]
        ring
  have hfibsum (R : Ideal (𝓞 K)) (hR : R ∈ S.image rad) :
      (∑ v ∈ S with rad v = R, 1 / (Ideal.absNorm (rad v) : ℝ)) ≤
        C * Y ^ (3 * e) * (1 / (Ideal.absNorm R : ℝ)) := by
    calc
      _ = ∑ _v ∈ S with rad _v = R, 1 / (Ideal.absNorm R : ℝ) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [(Finset.mem_filter.mp hv).2]
      _ = ((S.filter (fun v => rad v = R)).card : ℝ) / (Ideal.absNorm R : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ (C * Y ^ (3 * e)) / (Ideal.absNorm R : ℝ) :=
        div_le_div_of_nonneg_right (hcard R hR) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hsum := Finset.sum_fiberwise_of_maps_to
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem rad hv)
    (fun v => 1 / (Ideal.absNorm (rad v) : ℝ))
  change (∑ v ∈ S, 1 / (Ideal.absNorm (rad v) : ℝ)) ≤ _
  rw [← hsum]
  calc
    _ ≤ ∑ R ∈ S.image rad, C * Y ^ (3 * e) * (1 / (Ideal.absNorm R : ℝ)) :=
      Finset.sum_le_sum hfibsum
    _ = C * Y ^ (3 * e) * (∑ R ∈ S.image rad, 1 / (Ideal.absNorm R : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ C * Y ^ (3 * e) *
        (2 * idealCountConstant K * (columnDyadicLength Y + 1 : ℝ) / (Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (divisible_inverse_norm_sum (S.image rad) s hs0 hR0 hdiv Y hRN) (by positivity)
    _ = _ := by ring

theorem column_dyadic_length_log_bound (B Z : ℝ) (hB : 0 ≤ B) (hZ : 1 ≤ Z) :
    (columnDyadicLength (Z ^ B) + 1 : ℝ) ≤
      (2 + B / Real.log 2) * (1 + Real.log Z) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := (Nat.ceil_lt_add_one
    (div_nonneg (mul_nonneg hB hlog) hlog2.le)).le
  have hlength : (columnDyadicLength (Z ^ B) : ℝ) ≤
      (B / Real.log 2) * Real.log Z + 1 := by
    rw [columnDyadicLength, Real.log_rpow hz]
    convert hceil using 1 <;> ring
  have hB' : 0 ≤ B / Real.log 2 := div_nonneg hB hlog2.le
  nlinarith

theorem log_linear_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → 1 + Real.log Z ≤ C * Z ^ δ := by
  refine ⟨1 + 1 / δ, by positivity, ?_⟩
  intro Z hZ
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 1 ≤ Z ^ δ := Real.one_le_rpow hZ hδ.le
  have hl := Real.log_le_rpow_div hz.le hδ
  calc
    _ ≤ Z ^ δ + Z ^ δ / δ := add_le_add hp hl
    _ = _ := by ring

/-- Uniform aggregate mass of the actual complete common-support labels.
All multiplicities and all prime-subset allocations remain in the sum. -/
theorem common_radical_harmonic_mass (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ s : Ideal (𝓞 K),
      Squarefree s → s ≠ 0 → ∀ S : Finset (Label K), (∀ v ∈ S, Valid s v) →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B) →
      (∑ v ∈ S, 1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) ≤
        C * Z ^ δ / (Ideal.absNorm s : ℝ) := by
  let e : ℝ := δ / (6 * (B + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hbudget : 3 * B * e + δ / 2 ≤ δ := by
    have hh : e * (6 * (B + 1)) = δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C, hC, hbound⟩ := common_radical_harmonic_mass_dyadic (K := K) e he
  obtain ⟨D, hD, hlog⟩ := log_linear_subpower (δ / 2) (by positivity)
  let L : ℝ := 2 + B / Real.log 2
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C * L * D, mul_pos (mul_pos hC hL) hD, ?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hsn : 0 < (Ideal.absNorm s : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hY : 0 < Z ^ B := Real.rpow_pos_of_pos hz B
  have hfactor : 0 ≤ C * (Z ^ B) ^ (3 * e) := mul_nonneg hC.le (Real.rpow_nonneg hY.le _)
  calc
    _ ≤ C * (Z ^ B) ^ (3 * e) * (columnDyadicLength (Z ^ B) + 1 : ℝ) /
        (Ideal.absNorm s : ℝ) := hbound s hs hs0 S hS (Z ^ B) hY hN
    _ ≤ C * (Z ^ B) ^ (3 * e) * (L * (1 + Real.log Z)) /
        (Ideal.absNorm s : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (column_dyadic_length_log_bound B Z hB hZ) hfactor) hsn.le
    _ ≤ C * (Z ^ B) ^ (3 * e) * (L * (D * Z ^ (δ / 2))) /
        (Ideal.absNorm s : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlog Z hZ) hL.le) hfactor) hsn.le
    _ = (C * L * D) * Z ^ (3 * B * e + δ / 2) / (Ideal.absNorm s : ℝ) := by
      rw [← Real.rpow_mul hz.le, show B * (3 * e) = 3 * B * e by ring, Real.rpow_add hz]
      ring
    _ ≤ (C * L * D) * Z ^ δ / (Ideal.absNorm s : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ hbudget) (mul_pos (mul_pos hC hL) hD).le) hsn.le

theorem min_le_sqrt_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y ≤ Real.sqrt (x * y) := by
  apply (Real.le_sqrt (le_min hx hy) (mul_nonneg hx hy)).mpr
  rcases le_total x y with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- The paired common-support weight has the same uniform mass bound. -/
theorem common_harmonic_mass (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ s : Ideal (𝓞 K),
      Squarefree s → s ≠ 0 → ∀ S : Finset (Label K), (∀ v ∈ S, Valid s v) →
      (∀ v ∈ S, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B) →
      (∑ v ∈ S, 1 / Real.sqrt ((Ideal.absNorm v.1.1 : ℝ) * Ideal.absNorm v.1.2)) ≤
        C * Z ^ δ / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := common_radical_harmonic_mass (K := K) B δ hB hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ s hs hs0 S hS hN
  apply le_trans _ (hbound Z hZ s hs hs0 S hS hN)
  apply Finset.sum_le_sum
  intro v hv
  have hr : 0 < (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero v.1.1 v.1.2))
  apply one_div_le_one_div_of_le hr
  exact (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
    (min_le_sqrt_mul _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

end

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.common_radical_harmonic_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.common_harmonic_mass
