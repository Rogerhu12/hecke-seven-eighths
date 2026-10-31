import DedekindZetaZeroFree.CharacterSums.Gauss.PositiveDepthLocalSums

/-!
# The actual local amplifier table

The local coefficient is the existing finite residue sum `Ctk C p n 0 M`,
centrally normalized by `Q(p)^n`.  Its original and sixth-power frequencies
agree away from the three positive valuations `1`, `6`, and `7`.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree
open LocalFiniteSums CanonicalLocalGaussTable LocalFiniteSumCompatibility

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- Central normalization of the actual local finite Gauss coefficient. -/
def centralPrimePower (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n M : ℕ) : ℂ :=
  Ctk C p n 0 M / (Q p : ℂ) ^ n

theorem primeNorm_pos (p : ExteriorPrime A) : 0 < Q p :=
  A.exteriorNorm_pos (primeIdeal p)

theorem centralPrimePower_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (M : ℕ) : centralPrimePower C p 0 M = 1 := by
  simp [centralPrimePower, Ctk_zero_zero]

/-- This displays the finite sum being used, including its nonunit zeros. -/
theorem centralPrimePower_eq_finite_sum (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n M : ℕ) :
    centralPrimePower C p n M =
      (∑ v : Residue C p n, maskedPower C p n (n : ℤ) v *
        psi C p n (residueMap C p n (generator C p ^ M) * v)) / (Q p : ℂ) ^ n := by
  rw [centralPrimePower, Ctk_kzero_sum]

theorem centralPrimePower_positive (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n M : ℕ) (hn : 0 < n) :
    centralPrimePower C p n M =
      if n - 1 ≤ M then
        T C p (n : ℤ) (residueMap C p 1 (generator C p ^ (M - (n - 1)))) / (Q p : ℂ)
      else 0 := by
  have hQ : (Q p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (primeNorm_pos p).ne'
  rw [centralPrimePower_eq_finite_sum,
    PrimePowerFourier.masked_fourier_prime_power C p n M hn (n : ℤ)]
  split_ifs with hM
  · have hp : (Q p : ℂ) ^ n = (Q p : ℂ) ^ (n - 1) * (Q p : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [hp]
    field_simp [hQ] <;> ring
  · simp

theorem tau_seven_eq_one (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : tau C p 7 = tau C p 1 := by
  unfold tau
  rw [T_eq_finiteField, T_eq_finiteField]
  rfl

theorem centralPrimePower_unit_frequency (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    centralPrimePower C p n 0 =
      if n = 0 then 1 else if n = 1 then tau C p 1 / (Q p : ℂ) else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [centralPrimePower_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  rw [if_neg hn0]
  by_cases hn1 : n = 1
  · subst n
    rw [if_pos rfl, centralPrimePower_positive C p 1 0 (by decide)]
    simp [tau]
  · rw [if_neg hn1, centralPrimePower_positive C p n 0 hn]
    exact if_neg (by omega)

theorem centralPrimePower_sixth_frequency (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    centralPrimePower C p n 6 =
      if n = 0 then 1
      else if n = 6 then 1 - (Q p : ℂ)⁻¹
      else if n = 7 then tau C p 1 / (Q p : ℂ)
      else 0 := by
  have hQ : (Q p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (primeNorm_pos p).ne'
  by_cases hn0 : n = 0
  · subst n
    simp [centralPrimePower_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  rw [if_neg hn0]
  by_cases hn6 : n = 6
  · subst n
    rw [if_pos rfl, centralPrimePower_positive C p 6 6 (by decide),
      if_pos (by decide), T_generator_power]
    norm_num
    field_simp [hQ] <;> ring
  rw [if_neg hn6]
  by_cases hn7 : n = 7
  · subst n
    rw [if_pos rfl, centralPrimePower_positive C p 7 6 (by decide),
      if_pos (by decide), T_generator_power]
    norm_num [tau_seven_eq_one]
  rw [if_neg hn7, centralPrimePower_positive C p n 6 hn]
  by_cases hM : n - 1 ≤ 6
  · rw [if_pos hM, T_generator_power, if_neg (by omega), if_neg (by omega)]
    simp
  · exact if_neg hM

/-- Only valuations `1`, `6`, and `7` change under one sixth-power insertion. -/
theorem centralPrimePower_difference_support (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hne : centralPrimePower C p n 0 ≠ centralPrimePower C p n 6) :
    n = 1 ∨ n = 6 ∨ n = 7 := by
  by_contra h
  push_neg at h
  apply hne
  rw [centralPrimePower_unit_frequency, centralPrimePower_sixth_frequency]
  simp [h.1, h.2.1, h.2.2]

theorem centralPrimePower_one_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    ‖centralPrimePower C p 1 0‖ ^ 2 = (Q p)⁻¹ := by
  have hQ := primeNorm_pos p
  rw [centralPrimePower_unit_frequency]
  norm_num only
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hQ.le, div_pow,
    norm_tau_of_not_six_dvd C p 1 (by norm_num), Real.sq_sqrt hQ.le]
  field_simp [hQ.ne'] <;> ring

theorem centralPrimePower_six_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    ‖centralPrimePower C p 6 6‖ ^ 2 = (1 - (Q p)⁻¹) ^ 2 := by
  rw [centralPrimePower_sixth_frequency]
  norm_num only
  rw [← Complex.ofReal_one, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem centralPrimePower_seven_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    ‖centralPrimePower C p 7 6‖ ^ 2 = (Q p)⁻¹ := by
  rw [centralPrimePower_sixth_frequency]
  norm_num only
  have h := centralPrimePower_one_norm_sq C p
  rw [centralPrimePower_unit_frequency] at h
  simpa using h

/-- The signed correction retains the whole complex coefficient before
the three valuation rows are estimated. -/
theorem centralPrimePower_amplifier_identity (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    centralPrimePower C p n 0 = centralPrimePower C p n 6 +
      (if n = 1 then tau C p 1 / (Q p : ℂ) else 0) -
      (if n = 6 then 1 - (Q p : ℂ)⁻¹ else 0) -
      (if n = 7 then tau C p 1 / (Q p : ℂ) else 0) := by
  rw [centralPrimePower_unit_frequency, centralPrimePower_sixth_frequency]
  by_cases h0 : n = 0
  · subst n
    norm_num
  by_cases h1 : n = 1
  · subst n
    norm_num
  by_cases h6 : n = 6
  · subst n
    norm_num
  by_cases h7 : n = 7
  · subst n
    norm_num
  simp [h0, h1, h6, h7]

/-- Exact squared sizes of all three correction rows. -/
theorem centralPrimePower_difference_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    ‖centralPrimePower C p n 0 - centralPrimePower C p n 6‖ ^ 2 =
      if n = 1 then (Q p)⁻¹
      else if n = 6 then (1 - (Q p)⁻¹) ^ 2
      else if n = 7 then (Q p)⁻¹ else 0 := by
  by_cases h1 : n = 1
  · subst n
    simpa [centralPrimePower_unit_frequency, centralPrimePower_sixth_frequency] using
      centralPrimePower_one_norm_sq C p
  by_cases h6 : n = 6
  · subst n
    simpa [centralPrimePower_unit_frequency, centralPrimePower_sixth_frequency] using
      centralPrimePower_six_norm_sq C p
  by_cases h7 : n = 7
  · subst n
    simpa [centralPrimePower_unit_frequency, centralPrimePower_sixth_frequency] using
      centralPrimePower_seven_norm_sq C p
  have he : centralPrimePower C p n 0 = centralPrimePower C p n 6 := by
    by_contra hc
    rcases centralPrimePower_difference_support C p n hc with h | h | h
    · exact h1 h
    · exact h6 h
    · exact h7 h
  simp [h1, h6, h7, he]

/-- The same finite coefficient at an arbitrary residue frequency. -/
def centralPrimePowerAt (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (h : Residue C p n) : ℂ :=
  (∑ v : Residue C p n, maskedPower C p n (n : ℤ) v * psi C p n (h * v)) /
    (Q p : ℂ) ^ n

theorem centralPrimePowerAt_generator (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n M : ℕ) :
    centralPrimePowerAt C p n (residueMap C p n (generator C p ^ M)) =
      centralPrimePower C p n M := by
  rw [centralPrimePower_eq_finite_sum]
  rfl

theorem maskedPower_multiplicative (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (a : ℤ) (x y : Residue C p n) :
    maskedPower C p n a (x * y) = maskedPower C p n a x * maskedPower C p n a y := by
  by_cases hn : n = 0
  · subst n
    simp [maskedPower_zero_depth]
  · simp only [maskedPower_eq_reduction C p n hn, map_mul]

theorem maskedPower_unit_norm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (a : ℤ) (u : (Residue C p n)ˣ) :
    ‖maskedPower C p n a u‖ = 1 := by
  by_cases hn : n = 0
  · subst n
    simp [maskedPower_zero_depth]
  letI : Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _
  letI : Fintype (A.R ⧸ A.extendIdeal (primeIdeal p)) := Fintype.ofFinite _
  let v : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ :=
    Units.map (reduction C p n hn).toMonoidHom u
  rw [maskedPower_eq_reduction C p n hn]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity
    ((chi (σ := σ) p ^ SArithmeticData.sexticExponent a).apply_mem_rootsOfUnity v)

/-- Unit multiplication transports the full local coefficient by its exact phase. -/
theorem centralPrimePowerAt_unit_covariance (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (u : (Residue C p n)ˣ) (h : Residue C p n) :
    maskedPower C p n (n : ℤ) u * centralPrimePowerAt C p n ((u : Residue C p n) * h) =
      centralPrimePowerAt C p n h := by
  have hs : maskedPower C p n (n : ℤ) u *
      (∑ v : Residue C p n, maskedPower C p n (n : ℤ) v *
        psi C p n (((u : Residue C p n) * h) * v)) =
      ∑ v : Residue C p n, maskedPower C p n (n : ℤ) v * psi C p n (h * v) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ v : Residue C p n,
          maskedPower C p n (n : ℤ) ((u : Residue C p n) * v) *
            psi C p n (h * ((u : Residue C p n) * v)) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [maskedPower_multiplicative]
        have he : ((u : Residue C p n) * h) * v =
            h * ((u : Residue C p n) * v) := by ring
        rw [he]
        ring
      _ = _ := Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun _ => rfl)
  unfold centralPrimePowerAt
  rw [← mul_div_assoc, hs]

theorem centralPrimePowerAt_unit_norm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (u : (Residue C p n)ˣ) (h : Residue C p n) :
    ‖centralPrimePowerAt C p n ((u : Residue C p n) * h)‖ =
      ‖centralPrimePowerAt C p n h‖ := by
  have he := congrArg norm (centralPrimePowerAt_unit_covariance C p n u h)
  simpa only [norm_mul, maskedPower_unit_norm, one_mul] using he

theorem maskedPower_sixth_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (a : ℤ) (u : (Residue C p n)ˣ) :
    maskedPower C p n a ((u : Residue C p n) ^ 6) = 1 := by
  by_cases hn : n = 0
  · subst n
    simp [maskedPower_zero_depth]
  let v : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ :=
    Units.map (reduction C p n hn).toMonoidHom u
  have h6 := chi_unit_sixth (σ := σ) p (v : A.R ⧸ A.extendIdeal (primeIdeal p)) v.isUnit
  rw [maskedPower_eq_reduction C p n hn, map_pow, map_pow]
  change ((chi (σ := σ) p ^ SArithmeticData.sexticExponent a) v) ^ 6 = 1
  rw [MulChar.pow_apply_coe, ← pow_mul, mul_comm _ 6, pow_mul, h6, one_pow]

/-- Sixth powers of units preserve even the phase of the full local transform. -/
theorem centralPrimePowerAt_sixth_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (u : (Residue C p n)ˣ) (h : Residue C p n) :
    centralPrimePowerAt C p n ((u : Residue C p n) ^ 6 * h) =
      centralPrimePowerAt C p n h := by
  have he := centralPrimePowerAt_unit_covariance C p n (u ^ 6) h
  simpa only [Units.val_pow_eq_pow_val, maskedPower_sixth_unit, one_mul] using he

theorem centralPrimePowerAt_unit_difference_support (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (u : (Residue C p n)ˣ)
    (hne : centralPrimePowerAt C p n ((u : Residue C p n) *
        residueMap C p n (generator C p ^ 0)) ≠
      centralPrimePowerAt C p n ((u : Residue C p n) *
        residueMap C p n (generator C p ^ 6))) :
    n = 1 ∨ n = 6 ∨ n = 7 := by
  apply centralPrimePower_difference_support C p n
  intro he
  apply hne
  have hc := centralPrimePowerAt_unit_covariance C p n u
  have hunit : maskedPower C p n (n : ℤ) u ≠ 0 := by
    intro hz
    have hh := maskedPower_unit_norm C p n (n : ℤ) u
    simp [hz] at hh
  apply mul_left_cancel₀ hunit
  rw [hc, hc, centralPrimePowerAt_generator, centralPrimePowerAt_generator, he]

theorem centralPrimePowerAt_one_unit_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : (Residue C p 1)ˣ) :
    ‖centralPrimePowerAt C p 1 ((u : Residue C p 1) *
      residueMap C p 1 (generator C p ^ 0))‖ ^ 2 = (Q p)⁻¹ := by
  rw [centralPrimePowerAt_unit_norm, centralPrimePowerAt_generator,
    centralPrimePower_one_norm_sq]

theorem centralPrimePowerAt_six_unit_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : (Residue C p 6)ˣ) :
    ‖centralPrimePowerAt C p 6 ((u : Residue C p 6) *
      residueMap C p 6 (generator C p ^ 6))‖ ^ 2 = (1 - (Q p)⁻¹) ^ 2 := by
  rw [centralPrimePowerAt_unit_norm, centralPrimePowerAt_generator,
    centralPrimePower_six_norm_sq]

theorem centralPrimePowerAt_seven_unit_norm_sq (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : (Residue C p 7)ˣ) :
    ‖centralPrimePowerAt C p 7 ((u : Residue C p 7) *
      residueMap C p 7 (generator C p ^ 6))‖ ^ 2 = (Q p)⁻¹ := by
  rw [centralPrimePowerAt_unit_norm, centralPrimePowerAt_generator,
    centralPrimePower_seven_norm_sq]

end HeckeSkeleton.Moments.EngineStep
