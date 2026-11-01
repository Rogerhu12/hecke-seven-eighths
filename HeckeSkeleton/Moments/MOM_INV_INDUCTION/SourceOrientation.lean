import HeckeSkeleton.Moments.MOM_INV_INDUCTION.BoundedScale
import HeckeGeneral.Analysis.HeckeConjugation

/-!
# Align the moving inverse orientation without changing the moment

The original prime slots have moving character chi, while the inverse
column permits either chi or chi inverse. In the negative case only the
inverse factor is conjugated. Its norm is unchanged even when multiplied
by the unchanged original slot product. The resulting inverse column has
positive moving orientation, conjugated fixed background and conjugated
test, with the same full support, row enumeration and original zero mask.

This is an exact identity of the original finite moment energies. It
does not assert an equality of the un-conjugated marked polynomials or
change the source calibration predicate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators ComplexConjugate

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Complex conjugation keeps the actual finite support of every row
and every independent scale. -/
def sourceConjugateTest (W : IdealTest K) : IdealTest K where
  profile u t y := conj (W.profile u t y)
  support := W.support
  support_spec u t D I := by
    rw [W.support_spec]
    simp only [map_ne_zero]

theorem sourceConjugateTest_norm (W : IdealTest K) (u : NonzeroIdeal K) (t y : ℝ) :
    ‖(sourceConjugateTest W).profile u t y‖ = ‖W.profile u t y‖ :=
  Complex.norm_conj _

/-- Unitary zero-extended coefficients still conjugate to their
inverse at ramified primes; zeros are not replaced by units. -/
theorem hecke_coefficient_inverse_eq_conj (χ : HeckeCharacter K) (I : NonzeroIdeal K) :
    (heckeIdealCoefficient K χ I)⁻¹ = conj (heckeIdealCoefficient K χ I) := by
  rcases hecke_coefficient_zero_or_norm_one χ I with hz | hn
  · simp [hz]
  · exact Complex.inv_eq_conj hn

theorem directed_coefficient_conjugate (χ : HeckeCharacter K)
    (I : NonzeroIdeal K) (e : ℤ) :
    heckeIdealCoefficient K χ I ^ (-e) = conj (heckeIdealCoefficient K χ I ^ e) := by
  rw [map_zpow₀, ← hecke_coefficient_inverse_eq_conj, inv_zpow, zpow_neg]

/-- Only the inverse factor is conjugated. The row character, actual
prime slots, complete row pool and common zero mask are unchanged. -/
def conjugateInverseModel (d : MomentData K ω ψ) : MomentData K ω ψ :=
  { d with
    inverseBackground := d.inverseBackground⁻¹
    direction := -d.direction
    direction_spec := by
      rcases d.direction_spec with hd | hd
      · right; simp [hd]
      · left; simp [hd]
    directed_background := by
      simpa only [neg_neg, inv_zpow, zpow_neg] using d.directed_background
    inverseTest := sourceConjugateTest d.inverseTest }

@[simp] theorem conjugateInverseModel_mask (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    maskValue (conjugateInverseModel d) u I = maskValue d u I := rfl

@[simp] theorem source_mask_conjugate (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    conj (maskValue d u I) = maskValue d u I := by
  unfold maskValue
  split_ifs <;> simp

/-- The normalization, Mobius coefficient, full support and original
mask are all retained in this literal polynomial conjugation. -/
theorem conjugateInverseModel_polynomial (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (conjugateInverseModel d) u D t =
      conj (inversePolynomial d u D t) := by
  simp only [inversePolynomial, conjugateInverseModel, sourceConjugateTest,
    map_mul, map_sum, map_inv₀, map_intCast, Complex.conj_ofReal,
    heckeIdealCoefficient_inv, directed_coefficient_conjugate, source_mask_conjugate,
    maskValue]
  simp only [apply_ite, map_one, map_zero, mul_ite]

@[simp] theorem conjugateInverseModel_slots (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct (conjugateInverseModel d) u Z t = slotProduct d u Z t := rfl

/-- Conjugating only the inverse factor preserves its product norm
with the original, unmodified prime slots. -/
theorem conjugateInverseModel_marked_norm (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D Z t : ℝ) :
    ‖inversePolynomial (conjugateInverseModel d) u D t *
        slotProduct (conjugateInverseModel d) u Z t‖ ^ 2 =
      ‖inversePolynomial d u D t * slotProduct d u Z t‖ ^ 2 := by
  rw [conjugateInverseModel_polynomial, conjugateInverseModel_slots]
  simp only [norm_mul, Complex.norm_conj]

theorem conjugateInverseModel_energy (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) :
    inverseEnergy (conjugateInverseModel d) a Z t = inverseEnergy d a Z t := by
  unfold inverseEnergy
  apply Finset.sum_congr rfl
  intro u _
  exact conjugateInverseModel_marked_norm d u (Z ^ a.r) Z t

/-- A canonical positive-orientation representative of the same
actual marked energy. This choice depends only on the fixed direction. -/
def positiveInverseModel (d : MomentData K ω ψ) : MomentData K ω ψ :=
  if d.direction = 1 then d else conjugateInverseModel d

theorem positiveInverseModel_direction (d : MomentData K ω ψ) :
    (positiveInverseModel d).direction = 1 := by
  by_cases hd : d.direction = 1
  · simpa only [positiveInverseModel, if_pos hd] using hd
  · have hm := d.direction_spec.resolve_right hd
    rw [positiveInverseModel, if_neg hd]
    change -d.direction = 1
    rw [hm]
    norm_num

theorem positiveInverseModel_energy (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) :
    inverseEnergy (positiveInverseModel d) a Z t = inverseEnergy d a Z t := by
  unfold positiveInverseModel
  split_ifs
  · rfl
  · exact conjugateInverseModel_energy d a Z t

theorem positiveInverseModel_complete_energy (d : MomentData K ω ψ) (U D : ℝ) :
    completeIndependentInverseEnergy (positiveInverseModel d) U D =
      completeIndependentInverseEnergy d U D := by
  unfold positiveInverseModel
  split_ifs
  · rfl
  · unfold completeIndependentInverseEnergy
    apply Finset.sum_congr rfl
    intro u _
    rw [conjugateInverseModel_polynomial, Complex.norm_conj]

theorem positiveInverseModel_profile_norm (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (t y : ℝ) :
    ‖(positiveInverseModel d).inverseTest.profile u t y‖ =
      ‖d.inverseTest.profile u t y‖ := by
  unfold positiveInverseModel
  split_ifs
  · rfl
  · exact sourceConjugateTest_norm d.inverseTest u t y

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
