import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Finite residue-field calculations for exterior theta digits

This module proves the finite sums on the right-hand side of the local
Whittaker/Weyl identity.  `finiteWeylSum` is a finite sum, not a definition of
an actual Whittaker coefficient.  Identifying it with the project's
`localDigit` is a separate representation-theoretic step.

The normalization is that an additive character is primitive, a sextic
multiplicative character has order six, and `W 0 = 1`.

The zero-mark Fourier observation is also present in OpenAI/math,
commit fd4aeeb2, `OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean`.
The proofs below use only mathlib.
-/

namespace HeckeSkeleton.ThetaLocal

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

/-- The uniform digit weight for a divisibility mark. -/
def uniformDigit (_v : F) : ℂ := (Fintype.card F : ℂ)⁻¹

/-- The Gauss denominator in the ordinary digit of exponent `j`. -/
def digitTau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  gaussSum (χ⁻¹ ^ j) ψ

/-- Ordinary Fourier digit, including the whole-index coprimality digit. -/
def ordinaryDigit (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (v : F) : ℂ :=
  if j = 0 then
    if v = 0 then 1 - (Fintype.card F : ℂ)⁻¹ else -(Fintype.card F : ℂ)⁻¹
  else (digitTau χ ψ j)⁻¹ * (χ⁻¹ ^ j) v

/-- The residue-field sum supplied by the local Weyl formula at valuation `e`.
For `e > 0`, the additive character on the integral argument is one. -/
def finiteWeylSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (β : F → ℂ) (e : ℕ) (t : Fˣ) : ℂ :=
  W e * χ t ^ (4 + 2 * e) *
    ∑ v : F, β v * (χ ^ 4) v * (if e = 0 then ψ ((t : F) / v) else 1)

/-- Additive orthogonality with the correct uniform normalization. -/
theorem uniform_digit_fourier (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (t : F) :
    (∑ v : F, uniformDigit v * ψ (t * v)) = if t = 0 then 1 else 0 := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [uniformDigit, ← Finset.mul_sum]
  simp_rw [mul_comm t]
  rw [AddChar.sum_mulShift t hψ]
  split_ifs <;> simp [hq]

/-- The inactive digit has scalar `q⁻¹`. -/
theorem uniform_digit_zero : uniformDigit (0 : F) = (Fintype.card F : ℂ)⁻¹ := rfl

/-- The ordinary exponent-zero inactive digit has scalar `1-q⁻¹`. -/
theorem ordinary_digit_zero_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    ordinaryDigit χ ψ 0 0 = 1 - (Fintype.card F : ℂ)⁻¹ := by
  simp [ordinaryDigit]

/-- Inversion followed by scaling evaluates the inverse-argument finite sum.
This is the substitution `x=t/v`, with the zero term killed by `η 0 = 0`. -/
theorem inverse_argument_gauss (η : MulChar F ℂ) (ψ : AddChar F ℂ) (t : Fˣ) :
    (∑ v : F, η v * ψ ((t : F) / v)) = η t * gaussSum η⁻¹ ψ := by
  calc
    _ = gaussSum η⁻¹ (ψ.mulShift (t : F)) := by
      unfold gaussSum
      refine Fintype.sum_bijective (fun v : F => v⁻¹) inv_bijective _ _ ?_
      intro v
      simp only [MulChar.inv_apply', inv_inv, AddChar.mulShift_apply, div_eq_mul_inv]
    _ = _ := by rw [gaussSum_mulShift_eq, inv_inv]

/-- Character orthogonality, retaining the exceptional trivial character. -/
theorem multiplicative_character_sum (η : MulChar F ℂ) :
    (∑ v : F, η v) = if η = 1 then (Fintype.card Fˣ : ℂ) else 0 := by
  by_cases hη : η = 1
  · simp [hη, MulChar.sum_one_eq_card_units]
  · simp [hη, MulChar.sum_eq_zero_of_ne_one hη]

/-- The valuation-zero Weyl sum for any scalar multiple of a character. -/
theorem finite_weyl_char_zero (χ η : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (c : ℂ) (t : Fˣ) :
    finiteWeylSum χ ψ W (fun v => c * η v) 0 t =
      W 0 * χ t ^ 4 * c * (η * χ ^ 4) t * gaussSum (η * χ ^ 4)⁻¹ ψ := by
  have hs : (∑ v : F, (c * η v) * (χ ^ 4) v * ψ ((t : F) / v)) =
      c * ((η * χ ^ 4) t * gaussSum (η * χ ^ 4)⁻¹ ψ) := by
    rw [← inverse_argument_gauss, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [MulChar.mul_apply]
    ring
  simp only [finiteWeylSum, Nat.mul_zero, Nat.add_zero, if_pos rfl, ite_true, hs]
  ring

/-- The positive-valuation Weyl sum for any scalar multiple of a character. -/
theorem finite_weyl_char_positive (χ η : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (c : ℂ) (e : ℕ) (he : e ≠ 0) (t : Fˣ) :
    finiteWeylSum χ ψ W (fun v => c * η v) e t =
      W e * χ t ^ (4 + 2 * e) * c *
        (if η * χ ^ 4 = 1 then (Fintype.card Fˣ : ℂ) else 0) := by
  have hs : (∑ v : F, (c * η v) * (χ ^ 4) v) =
      c * ∑ v : F, (η * χ ^ 4) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [MulChar.mul_apply]
    ring
  simp only [finiteWeylSum, if_neg he, mul_one, hs]
  rw [multiplicative_character_sum]
  ring

/-- A uniform mark vanishes at every positive valuation. -/
theorem mark_digit_positive (χ : MulChar F ℂ) (hχ4 : χ ^ 4 ≠ 1)
    (ψ : AddChar F ℂ) (W : ℕ → ℂ) (e : ℕ) (he : e ≠ 0) (t : Fˣ) :
    finiteWeylSum χ ψ W uniformDigit e t = 0 := by
  simp only [finiteWeylSum, uniformDigit, if_neg he, mul_one, ← Finset.mul_sum]
  rw [MulChar.sum_eq_zero_of_ne_one hχ4]
  ring

/-- Sextic inversion changes the fourth power to the second power. -/
theorem sextic_fourth_inverse (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1) :
    (χ ^ 4)⁻¹ = χ ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    χ ^ 4 * χ ^ 2 = χ ^ 6 := by rw [← pow_add]
    _ = 1 := hχ6

/-- The active mark at valuation zero has the raw Gauss factor `q⁻¹ G(χ²) χ(t)²`. -/
theorem mark_digit_zero (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1)
    (ψ : AddChar F ℂ) (W : ℕ → ℂ) (hW : W 0 = 1) (t : Fˣ) :
    finiteWeylSum χ ψ W uniformDigit 0 t =
      (Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ * χ t ^ 2 := by
  have ht6 : χ t ^ 6 = 1 := by
    have h := congrArg (fun ξ : MulChar F ℂ => ξ (t : F)) hχ6
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  have hs : (∑ v : F, (Fintype.card F : ℂ)⁻¹ * (χ ^ 4) v * ψ ((t : F) / v)) =
      (Fintype.card F : ℂ)⁻¹ * ((χ ^ 4) t * gaussSum (χ ^ 4)⁻¹ ψ) := by
    rw [← inverse_argument_gauss, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp only [finiteWeylSum, uniformDigit, Nat.mul_zero, Nat.add_zero, if_pos rfl, ite_true,
    hW, one_mul, hs]
  rw [sextic_fourth_inverse χ hχ6, MulChar.pow_apply_coe]
  calc
    _ = (Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ * (χ t ^ 6 * χ t ^ 2) := by ring
    _ = _ := by rw [ht6, one_mul]

/-- The complete finite-sum active-mark table. -/
theorem mark_digit_table (χ : MulChar F ℂ) (hχ6 : χ ^ 6 = 1) (hχ4 : χ ^ 4 ≠ 1)
    (ψ : AddChar F ℂ) (W : ℕ → ℂ) (hW : W 0 = 1) (e : ℕ) (t : Fˣ) :
    finiteWeylSum χ ψ W uniformDigit e t =
      if e = 0 then (Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ * χ t ^ 2 else 0 := by
  by_cases he : e = 0
  · subst e
    simpa using mark_digit_zero χ hχ6 ψ W hW t
  · simpa [he] using mark_digit_positive χ hχ4 ψ W e he t

/-- The exponent-zero ordinary active digit is the negative of a mark.
The apparent discrepancy at the zero digit disappears because `(χ⁴) 0 = 0`. -/
theorem ordinary_zero_eq_neg_mark (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (e : ℕ) (t : Fˣ) :
    finiteWeylSum χ ψ W (ordinaryDigit χ ψ 0) e t =
      -finiteWeylSum χ ψ W uniformDigit e t := by
  unfold finiteWeylSum
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = 0
  · simp [ordinaryDigit, uniformDigit, hv, MulChar.map_zero]
  · by_cases he : e = 0
    · simp [ordinaryDigit, uniformDigit, hv, he]
      <;> ring
    · simp [ordinaryDigit, uniformDigit, hv, he]
      <;> ring

/-- The ordinary valuation-zero table in exact character form.
For a sextic character, the unit factor is `χ(t)^(8-j)` and the numerator
is the Gauss sum of `χ^(j-4)`, as in `(can-weyl-table)`. -/
theorem ordinary_digit_table_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (hW : W 0 = 1) (j : ℕ) (hj : j ≠ 0) (t : Fˣ) :
    finiteWeylSum χ ψ W (ordinaryDigit χ ψ j) 0 t =
      (digitTau χ ψ j)⁻¹ * χ t ^ 4 * (χ⁻¹ ^ j * χ ^ 4) t *
        gaussSum (χ⁻¹ ^ j * χ ^ 4)⁻¹ ψ := by
  have hβ : ordinaryDigit χ ψ j = fun v => (digitTau χ ψ j)⁻¹ * (χ⁻¹ ^ j) v := by
    funext v
    simp [ordinaryDigit, hj]
  rw [hβ, finite_weyl_char_zero, hW]
  ring

/-- The ordinary positive-valuation table before reducing the exponent modulo six. -/
theorem ordinary_digit_table_positive (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (W : ℕ → ℂ) (j : ℕ) (hj : j ≠ 0) (e : ℕ) (he : e ≠ 0) (t : Fˣ) :
    finiteWeylSum χ ψ W (ordinaryDigit χ ψ j) e t =
      W e * χ t ^ (4 + 2 * e) * (digitTau χ ψ j)⁻¹ *
        (if χ⁻¹ ^ j * χ ^ 4 = 1 then (Fintype.card Fˣ : ℂ) else 0) := by
  have hβ : ordinaryDigit χ ψ j = fun v => (digitTau χ ψ j)⁻¹ * (χ⁻¹ ^ j) v := by
    funext v
    simp [ordinaryDigit, hj]
  rw [hβ]
  exact finite_weyl_char_positive χ (χ⁻¹ ^ j) ψ W _ e he t

/-- Among the six ordinary digits, only exponent four survives at positive valuation. -/
theorem sextic_positive_exception (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (j : ℕ) (hj : j < 6) :
    χ⁻¹ ^ j * χ ^ 4 = 1 ↔ j = 4 := by
  rw [inv_pow, inv_mul_eq_one, pow_inj_mod, hχ]
  simp [Nat.mod_eq_of_lt hj]

/-- The positive-valuation table in the paper's `j=4` form. -/
theorem ordinary_digit_table_positive_sextic (χ : MulChar F ℂ)
    (hχ : orderOf χ = 6) (ψ : AddChar F ℂ) (W : ℕ → ℂ)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (e : ℕ) (he : e ≠ 0) (t : Fˣ) :
    finiteWeylSum χ ψ W (ordinaryDigit χ ψ j) e t =
      W e * χ t ^ (4 + 2 * e) * (digitTau χ ψ j)⁻¹ *
        (if j = 4 then (Fintype.card Fˣ : ℂ) else 0) := by
  rw [ordinary_digit_table_positive χ ψ W j hj0 e he t,
    sextic_positive_exception χ hχ j hj6]
  by_cases h4 : j = 4 <;> simp [h4]

/-- Primitive Gauss denominators do not vanish. -/
theorem digit_tau_ne_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : χ⁻¹ ^ j ≠ 1) :
    digitTau χ ψ j ≠ 0 := by
  apply gaussSum_ne_zero_of_nontrivial _ hj hψ
  exact_mod_cast Fintype.card_ne_zero

/-- The square norm of a nonprincipal Gauss sum is exactly the residue cardinality. -/
theorem gauss_sum_norm_sq (η : MulChar F ℂ) (hη : η ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum η ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hη hψ
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  exact_mod_cast h

/-- Thus the norm is `sqrt(q)`, including the positivity assertion needed for normalization. -/
theorem gauss_sum_norm (η : MulChar F ℂ) (hη : η ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum η ψ‖ = Real.sqrt (Fintype.card F) := by
  rw [← gauss_sum_norm_sq η hη ψ hψ, Real.sqrt_sq (norm_nonneg _)]

end

end HeckeSkeleton.ThetaLocal
