import HeckeSkeleton.ThetaLocal.ExteriorUnitSums

/-! # The ordinary digit weights are the correct finite Fourier masks -/

namespace HeckeSkeleton.ThetaLocal.ResidueField

open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- Fourier inversion of every ordinary digit, with zero extension at the origin.
In particular, the zeroth digit transforms to the unit indicator, rather than
to the constant function one. -/
theorem digitMask_fourier (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (j : Fin 6) (t : F) :
    (∑ v : F, digitMask χ ψ j v * ψ (t * v)) = (χ ^ j.val) t := by
  by_cases hj : j.val = 0
  · have hm (v : F) : digitMask χ ψ j v =
        (if v = 0 then 1 else 0) - (Fintype.card F : ℂ)⁻¹ := by
      by_cases hv : v = 0 <;> simp [digitMask, hj, hv]
    simp_rw [hm, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs : (∑ v : F, ψ (t * v)) =
        if t = 0 then (Fintype.card F : ℂ) else 0 := by
      simpa [mul_comm] using AddChar.sum_mulShift t hψ
    rw [hs]
    by_cases ht : t = 0
    · simp [ht, hj, MulChar.map_zero, Fintype.card_ne_zero]
    · simp [ht, hj, MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)]
  · have hm (v : F) : digitMask χ ψ j v =
        (χ⁻¹ ^ j.val) v / localTau χ ψ j := by
      rw [digitMask_eq_ordinaryDigit]
      simp [ordinaryDigit, hj, ← localTau_eq_digitTau, div_eq_mul_inv, mul_comm]
    simp_rw [hm, div_mul_eq_mul_div, ← Finset.sum_div]
    by_cases ht : t = 0
    · have hc : χ⁻¹ ^ j.val ≠ 1 := by
        apply pow_ne_one_of_lt_orderOf hj
        simpa [orderOf_inv, hχ] using j.isLt
      subst t
      simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
      rw [MulChar.sum_eq_zero_of_ne_one hc]
      simp [MulChar.map_zero]
    · let u : Fˣ := Units.mk0 t ht
      have hs : (∑ v : F, (χ⁻¹ ^ j.val) v * ψ (t * v)) =
          (χ ^ j.val) t * localTau χ ψ j := by
        have h := gaussSum_mulShift_eq (χ⁻¹ ^ j.val) ψ u
        simpa [gaussSum, AddChar.mulShift_apply, u, inv_pow, localTau_eq_digitTau,
          digitTau] using h
      rw [hs, mul_div_cancel_right₀ _ (localTau_ne_zero χ hχ ψ hψ j hj)]

end
end HeckeSkeleton.ThetaLocal.ResidueField
