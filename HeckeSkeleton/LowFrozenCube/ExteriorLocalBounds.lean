import HeckeSkeleton.ThetaLocal.ExteriorUnitSums
import HeckeSkeleton.LowFrozenCube.LocalTable

/-!
# The three primitive frozen-table bounds from finite residue Gauss sums

These identities consume the literal residue-field tables already evaluated
by `ThetaLocal.ExteriorUnitSums`.  They supply the exact three scalar bounds
required by `PrimitiveLocalBounds`, including the two exceptional zero
valuation digits and the positive valuation prefactor.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.ExteriorLocalBounds

open HeckeSkeleton.ThetaLocal
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]
variable (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
variable (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)

def first : ℂ :=
  (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * ResidueField.gammaTwo χ ψ

def prefactor : ℂ :=
  ((Fintype.card F : ℂ) - 1) / ResidueField.localTau χ ψ ⟨4, by decide⟩

def atZero (j : ℕ) : ℂ :=
  ResidueField.localWeylScalar χ ψ ⟨j % 6, Nat.mod_lt _ (by decide)⟩ 0

theorem first_sq : ‖first χ ψ‖ ^ 2 = 1 / (Fintype.card F : ℝ) := by
  simp only [first, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ResidueField.gammaTwo_norm χ hχ ψ hψ,
    mul_one, inv_pow,
    Real.sq_sqrt (show 0 ≤ (Fintype.card F : ℝ) by positivity), one_div]

theorem prefactor_sq : ‖prefactor χ ψ‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hnum : ‖(Fintype.card F : ℂ) - 1‖ = (Fintype.card F : ℝ) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq1)]
  rw [prefactor, norm_div, hnum,
    ResidueField.localTau_norm χ hχ ψ hψ ⟨4, by decide⟩ (by decide),
    div_pow, Real.sq_sqrt hq.le]
  apply (div_le_iff₀ hq).mpr
  nlinarith

theorem zero_sq (j : Fin 6) :
    ‖ResidueField.localWeylScalar χ ψ j 0‖ ^ 2 =
      if j.val = 0 ∨ j.val = 4 then 1 / (Fintype.card F : ℝ) else 1 := by
  have hχ6 : χ ^ 6 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hψne : ψ ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    rw [ResidueField.localWeylScalar_zero_zero χ hχ6 ψ]
    simpa only [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ResidueField.gammaTwo_norm χ hχ ψ hψ,
      mul_one, inv_pow, Real.sq_sqrt hq.le, Fin.val_zero, true_or, if_true, one_div]
  · rw [ResidueField.localWeylScalar_zero_nonzero χ hχ6 ψ j hj0,
      norm_div, div_pow, ResidueField.localTau_norm χ hχ ψ hψ j hj0,
      Real.sq_sqrt hq.le]
    by_cases hj4 : j.val = 4
    · simp [hj4, gaussSum_one_left hψne]
    · have hn : (j.val + 2) % 6 ≠ 0 := by have := j.isLt; omega
      have hpow : χ ^ ((j.val + 2) % 6) ≠ 1 :=
        pow_ne_one_of_lt_orderOf hn (by rw [hχ]; exact Nat.mod_lt _ (by decide))
      rw [gauss_sum_norm _ hpow ψ hψ, Real.sq_sqrt hq.le]
      simp [hj0, hj4, ne_of_gt hq]

theorem atZero_sq (j : Fin 6) :
    ‖atZero χ ψ j.val‖ ^ 2 =
      if j.val = 0 ∨ j.val = 4 then 1 / (Fintype.card F : ℝ) else 1 := by
  have hj : (⟨j.val % 6, Nat.mod_lt j.val (by decide)⟩ : Fin 6) = j :=
    Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simpa only [atZero, hj] using zero_sq χ hχ ψ hψ j

theorem spherical_eq (e : ℕ) :
    ResidueField.sphericalDigit χ ψ e =
      LocalTable.sphericalScalar (Fintype.card F : ℂ) (first χ ψ) e := by
  unfold ResidueField.sphericalDigit LocalTable.sphericalScalar first
  split_ifs <;> simp_all only [mul_assoc]

/-- The frozen ordinary scalar is exactly the pre-existing finite Weyl
sum, at every valuation and every valid sextic digit. -/
theorem localWeyl_eq (j : Fin 6) (e : ℕ) :
    ResidueField.localWeylScalar χ ψ j e =
      LocalTable.ordinaryScalar (Fintype.card F : ℂ)
        (first χ ψ) (prefactor χ ψ) (atZero χ ψ) j.val e := by
  by_cases he : e = 0
  · subst e
    have hj : (⟨j.val % 6, Nat.mod_lt j.val (by decide)⟩ : Fin 6) = j :=
      Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simp only [LocalTable.ordinaryScalar, if_pos rfl, atZero, hj]
  · rw [ResidueField.localWeylScalar_positive χ hχ ψ j e he]
    by_cases hj : j.val = 4
    · have hj' : j = ⟨4, by decide⟩ := Fin.ext hj
      subst j
      simp only [LocalTable.ordinaryScalar, if_neg he, if_pos rfl,
        prefactor, spherical_eq χ ψ]
    · simp only [LocalTable.ordinaryScalar, if_neg he, if_neg hj]

#print axioms first_sq
#print axioms prefactor_sq
#print axioms zero_sq
#print axioms localWeyl_eq

end HeckeSkeleton.LowFrozenCube.ExteriorLocalBounds
