import FiniteFieldAffineCorrelation
import FiniteAffineCorrelationBound

/-! SOURCE ONLY, UNCOMPILED.

Artificial local extension for the residual columns in
quasi-riemann.tex:7113-7168. It agrees with the genuine affine congruence
sum on the coprime locus and is assigned zero when both columns vanish.
It is a separately defined function, not the genuine sum on all columns.
Every MulChar retains its zero mask, including the character power χ ^ 0.
This finite-field core makes no global radical-periodicity assertion.
-/

noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

/-- The artificial local extension Eχ. Only its coprime-column values are
identified with the original congruence sum. -/
def finiteFieldResidualCorrelationExtension (χ : MulChar F ℂ)
    (n₁ n₂ k : F) : ℂ :=
  if n₁ = 0 ∧ n₂ = 0 then 0 else affineCorrelation χ n₁ n₂ k

@[simp] theorem finiteFieldResidualCorrelationExtension_zero_zero
    (χ : MulChar F ℂ) (k : F) :
    finiteFieldResidualCorrelationExtension χ 0 0 k = 0 := by
  simp [finiteFieldResidualCorrelationExtension]

theorem finiteFieldResidualCorrelationExtension_eq_affineCorrelation
    (χ : MulChar F ℂ) (n₁ n₂ k : F) (hn : IsCoprime n₁ n₂) :
    finiteFieldResidualCorrelationExtension χ n₁ n₂ k =
      affineCorrelation χ n₁ n₂ k := by
  have hzero : ¬ (n₁ = 0 ∧ n₂ = 0) := by
    rcases Semifield.isCoprime_iff.mp hn with h₁ | h₂
    · exact fun h => h₁ h.1
    · exact fun h => h₂ h.2
  exact if_neg hzero

/-- Agreement with the literal pair sum, with its original minus sign. -/
theorem finiteFieldResidualCorrelationExtension_eq_sum
    (χ : MulChar F ℂ) (n₁ n₂ k : F) (hn : IsCoprime n₁ n₂) :
    finiteFieldResidualCorrelationExtension χ n₁ n₂ k =
      ∑ p : F × F, if n₂ * p.1 - n₁ * p.2 = k then
        χ p.1 * conj (χ p.2) else 0 := by
  rw [finiteFieldResidualCorrelationExtension_eq_affineCorrelation χ n₁ n₂ k hn]
  rfl

/-- This proof uses the true zero extension of a MulChar. In particular,
it applies to the principal MulChar and to arbitrary character powers. -/
private theorem norm_finiteFieldMulChar_apply_le_one
    (χ : MulChar F ℂ) (x : F) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    rw [χ.map_zero, norm_zero]
    exact zero_le_one
  · obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr hx
    apply le_of_eq
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u))

/-- Uniform bound for the artificial extension on all residual columns.
The genuine correlation estimate is used only on its coprime locus. -/
theorem norm_finiteFieldResidualCorrelationExtension_le_card
    (χ : MulChar F ℂ) (n₁ n₂ k : F) :
    ‖finiteFieldResidualCorrelationExtension χ n₁ n₂ k‖ ≤
      (Fintype.card F : ℝ) := by
  by_cases hzero : n₁ = 0 ∧ n₂ = 0
  · rw [finiteFieldResidualCorrelationExtension, if_pos hzero, norm_zero]
    exact Nat.cast_nonneg _
  · have hn : IsCoprime n₁ n₂ := by
      apply Semifield.isCoprime_iff.mpr
      by_cases h₁ : n₁ = 0
      · exact Or.inr (fun h₂ => hzero ⟨h₁, h₂⟩)
      · exact Or.inl h₁
    rw [finiteFieldResidualCorrelationExtension_eq_affineCorrelation χ n₁ n₂ k hn]
    exact norm_affineCorrelation_le_card χ
      (norm_finiteFieldMulChar_apply_le_one χ) n₁ n₂ hn k

end HeckeGeneral.Arithmetic.PeriodicFourier
