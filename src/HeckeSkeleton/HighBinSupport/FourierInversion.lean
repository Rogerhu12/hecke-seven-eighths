import HeckeSkeleton.HighBinSupport.PrimePowerFourier
/-!
# The physical finite convolution on arbitrary finite residue rings

The denominator-zero row is Fourier inversion. For a positive completed
index and denominator valuation one, the actual convolution becomes the
lifted character χ^(t-1). A nonzero residue kernel makes every higher
primitive denominator Gauss sum vanish at unit frequencies.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.FourierInversion
open HighBin.FiniteResidueFourier HighBin.PrimePowerFourier
open scoped BigOperators Classical ComplexConjugate

section Ring
variable {R : Type*} [CommRing R] [Fintype R]

/-- Exact inversion of the positive-sign finite Fourier transform. -/
theorem finite_fourier_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (h : R) :
    (∑ m : R, HighBin.FiniteResidueFourier.fourier ψ f (-m) * ψ (h * m)) = (Fintype.card R : ℂ) * f h := by
  simp only [HighBin.FiniteResidueFourier.fourier, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hx (x : R) :
      (∑ m : R, f x * ψ (-m * x) * ψ (h * m)) =
        f x * (if h - x = 0 then (Fintype.card R : ℂ) else 0) := by
    calc
      _ = f x * ∑ m : R, ψ (m * (h - x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [mul_assoc, ← ψ.map_add_eq_mul]
        congr 2
        ring
      _ = _ := by
        rw [AddChar.sum_mulShift (h - x) hψ]
        split_ifs <;> simp
  simp_rw [hx, sub_eq_zero]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ h]
  simp [mul_comm]

/-- The normalized convolution at completed index one recovers the
literal coefficient function, including its zero extension. -/
theorem normalized_finite_fourier_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (h : R) :
    (Fintype.card R : ℂ)⁻¹ * (∑ m : R, HighBin.FiniteResidueFourier.fourier ψ f (-m) * ψ (h * m)) = f h := by
  have hc : (Fintype.card R : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [finite_fourier_inversion ψ hψ f h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Ring

section Residue
variable {R F : Type*} [CommRing R] [Field F] [Fintype R] [Fintype F]

/-- A unit frequency cannot annihilate a nonzero residue kernel. -/
theorem unit_not_supported (π : R →+* F) (a : R) (ha : IsUnit a)
    (hker : ∃ b : R, π b = 0 ∧ b ≠ 0) : ¬ InFrequencySupport π a := by
  intro h
  obtain ⟨b, hb, hb0⟩ := hker
  exact hb0 (ha.mul_left_cancel (by simpa using h b hb))

/-- This is the arithmetic cancellation of all denominator powers k≥2:
those quotient rings have nonzero residue kernel and a primitive pairing. -/
theorem lifted_gauss_unit_zero (π : R →+* F) (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ) (a : R) (ha : IsUnit a)
    (hker : ∃ b : R, π b = 0 ∧ b ≠ 0) :
    HighBin.FiniteResidueFourier.fourier ψ (fun x => χ (π x)) a = 0 :=
  fourier_eq_zero_of_not_supported π ψ hψ _ a (unit_not_supported π a ha hker)

/-- The actual physical convolution for denominator valuation one. -/
def liftedConvolution (π : R →+* F) (χ ν : MulChar F ℂ)
    (φ : AddChar F ℂ) (ψ : AddChar R ℂ) (h : R) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ *
    ∑ m : R, gaussAt χ φ (-π m) * ν (π m) * ψ (h * m)

/-- Exact k=1 identification over the entire prime-power quotient, before
using its additive support or its kernel cardinality. -/
theorem liftedConvolution_eq (π : R →+* F) (χ ν : MulChar F ℂ) (hχ : χ ≠ 1)
    (φ : AddChar F ℂ) (ψ : AddChar R ℂ) (h : R) :
    liftedConvolution π χ ν φ ψ h =
      (χ⁻¹ (-1) * gaussSum χ φ / (Fintype.card F : ℂ)) *
        HighBin.FiniteResidueFourier.fourier ψ (fun x => (ν * χ⁻¹) (π x)) h := by
  unfold liftedConvolution HighBin.FiniteResidueFourier.fourier
  simp_rw [gaussAt_eq_inv_mul χ hχ φ]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [show -(π m) = (-1 : F) * π m by ring, map_mul]
  simp only [MulChar.mul_apply]
  ring

/-- The μ₁₂ normalization removes the minus-frequency phase. -/
theorem liftedConvolution_eq_of_neg_one (π : R →+* F) (χ ν : MulChar F ℂ)
    (hχ : χ ≠ 1) (hminus : χ⁻¹ (-1) = 1)
    (φ : AddChar F ℂ) (ψ : AddChar R ℂ) (h : R) :
    liftedConvolution π χ ν φ ψ h =
      (gaussSum χ φ / (Fintype.card F : ℂ)) *
        HighBin.FiniteResidueFourier.fourier ψ (fun x => (ν * χ⁻¹) (π x)) h := by
  rw [liftedConvolution_eq π χ ν hχ φ ψ h, hminus, one_mul]

#print axioms finite_fourier_inversion
#print axioms normalized_finite_fourier_inversion
#print axioms lifted_gauss_unit_zero
#print axioms liftedConvolution_eq
end Residue
end HighBin.FourierInversion
