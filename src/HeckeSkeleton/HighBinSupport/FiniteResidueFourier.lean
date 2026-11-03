import Mathlib.NumberTheory.GaussSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Actual residue-ring Fourier sums for the HIGHBIN Euler calibration

This module proves finite Fourier identities for arbitrary finite commutative
rings and finite residue fields. It does not assume the desired local Euler
factor as an input. The hypotheses are ring homomorphisms, a surjective residue
map, and actual additive/multiplicative characters.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.FiniteResidueFourier

open scoped BigOperators ComplexConjugate Classical

section FiniteRing

variable {R F : Type*} [CommRing R] [CommRing F] [Fintype R] [Fintype F]

/-- Literal (unnormalized, positive-sign) finite Fourier transform. -/
def fourier (ψ : AddChar R ℂ) (f : R → ℂ) (h : R) : ℂ :=
  ∑ x : R, f x * ψ (h * x)

/-- A lifted residue function vanishes in Fourier frequency whenever the
frequency character is nontrivial on the kernel of the residue map. This
is the prime-power conductor cancellation needed for the denominator
exponents `k ≥ 2` in the physical finite Fourier sum. -/
theorem fourier_pullback_eq_zero (π : R →+* F) (f : F → ℂ)
    (ψ : AddChar R ℂ) (h a : R) (ha : π a = 0) (hψa : ψ (h * a) ≠ 1) :
    fourier ψ (fun x => f (π x)) h = 0 := by
  let S : ℂ := fourier ψ (fun x => f (π x)) h
  have hshift : S = ψ (h * a) * S := by
    change (∑ x : R, f (π x) * ψ (h * x)) =
      ψ (h * a) * ∑ x : R, f (π x) * ψ (h * x)
    rw [Finset.mul_sum]
    symm
    refine Fintype.sum_bijective _ (Equiv.addRight a).bijective _ _ (fun x => ?_)
    change ψ (h * a) * (f (π x) * ψ (h * x)) = f (π (x + a)) * ψ (h * (x + a))
    rw [map_add, ha, add_zero, mul_add, ψ.map_add_eq_mul]
    ring
  have hz : (1 - ψ (h * a)) * S = 0 := by
    linear_combination hshift
  have hne : 1 - ψ (h * a) ≠ 0 := sub_ne_zero.mpr hψa.symm
  exact (mul_eq_zero.mp hz).resolve_left hne

/-- Choosing one representative per residue gives the exact residue/kernel
product decomposition. No coprimality between moduli is used. -/
def residueKernelEquiv (π : R →+* F) (hπ : Function.Surjective π) :
    R ≃ F × {x : R // π x = 0} where
  toFun x := (π x, ⟨x - Classical.choose (hπ (π x)), by
    change π (x - Classical.choose (hπ (π x))) = 0
    rw [map_sub, Classical.choose_spec (hπ (π x)), sub_self]⟩)
  invFun y := Classical.choose (hπ y.1) + y.2.val
  left_inv x := by
    change Classical.choose (hπ (π x)) + (x - Classical.choose (hπ (π x))) = x
    abel
  right_inv y := by
    rcases y with ⟨y, a, ha⟩
    have hz : π a = 0 := ha
    have hy : π (Classical.choose (hπ y) + a) = y := by
      rw [map_add, Classical.choose_spec (hπ y), hz, add_zero]
    apply Prod.ext
    · exact hy
    · apply Subtype.ext
      change Classical.choose (hπ y) + a -
        Classical.choose (hπ (π (Classical.choose (hπ y) + a))) = a
      rw [hy]
      abel

/-- Exact lifting of a residue-field sum, with the actual kernel cardinality.
This is the `q^(n-1)` multiplicity in an imprimitive prime-power Gauss sum. -/
theorem sum_pullback (π : R →+* F) (hπ : Function.Surjective π) (f : F → ℂ) :
    (∑ x : R, f (π x)) = (Nat.card {x : R // π x = 0} : ℂ) * ∑ y : F, f y := by
  letI : Fintype {x : R // π x = 0} := Fintype.ofFinite _
  have he : (∑ x : R, f (π x)) = ∑ y : F × {x : R // π x = 0}, f y.1 :=
    Fintype.sum_equiv (residueKernelEquiv π hπ) _ _ (fun _ => rfl)
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

/-- If the additive frequency descends to the residue field, the literal
prime-power Fourier sum is the kernel cardinality times that residue sum. -/
theorem fourier_pullback_of_descends (π : R →+* F) (hπ : Function.Surjective π)
    (f : F → ℂ) (ψ : AddChar R ℂ) (φ : AddChar F ℂ) (h : R)
    (hdesc : ∀ x : R, ψ (h * x) = φ (π x)) :
    fourier ψ (fun x => f (π x)) h =
      (Nat.card {x : R // π x = 0} : ℂ) * ∑ y : F, f y * φ y := by
  unfold fourier
  simp_rw [hdesc]
  exact sum_pullback π hπ (fun y => f y * φ y)

end FiniteRing

section FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- The actual shifted Gauss sum, including zero frequency. -/
def gaussAt (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (a : F) : ℂ :=
  gaussSum χ (ψ.mulShift a)

/-- The usual scaling identity is valid at zero as well when the
multiplicative character is nonprincipal. -/
theorem gaussAt_eq_inv_mul (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (a : F) :
    gaussAt χ ψ a = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst a
    simp only [gaussAt, AddChar.mulShift_zero, gaussSum_one_right hχ,
      MulChar.map_zero, zero_mul]
  · exact gaussSum_mulShift_eq χ ψ (Units.mk0 a ha)

/-- The actual residue Gauss sum has squared modulus equal to field size. -/
theorem gauss_norm_sq (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_conj', pow_two] using hr

/-- This is a statement about the finite sum, not a free bounded phase. -/
theorem gauss_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have h := gauss_norm_sq χ hχ ψ hψ
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card F by positivity)
  have hn := norm_nonneg (gaussSum χ ψ)
  have hr := Real.sqrt_nonneg (Fintype.card F : ℝ)
  nlinarith

/-- Normalized actual finite Gauss sum. -/
def normalizedGauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)

theorem normalizedGauss_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖normalizedGauss χ ψ‖ = 1 := by
  have hpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [normalizedGauss, norm_div, gauss_norm χ hχ ψ hψ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hpos)]
  exact div_self (Real.sqrt_pos.mpr hpos).ne'

/-- The finite-field part of the `k=1` physical convolution, written with
actual shifted Gauss sums and actual multiplicative characters. -/
def localConvolution (χ ν : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ m : F, gaussAt χ ψ (-m) * ν m * ψ (h * m)

/-- Exact finite Fourier identification, with the full zero extension.
For `ν = χ^t`, the new multiplicative character is `χ^(t-1)`. -/
theorem localConvolution_eq (χ ν : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (h : F) :
    localConvolution χ ν ψ h =
      χ⁻¹ (-1) * gaussSum χ ψ * gaussAt (ν * χ⁻¹) ψ h := by
  unfold localConvolution
  simp_rw [gaussAt_eq_inv_mul χ hχ ψ]
  change (∑ m : F, χ⁻¹ (-m) * gaussSum χ ψ * ν m * ψ (h * m)) =
    χ⁻¹ (-1) * gaussSum χ ψ * ∑ m : F, (ν * χ⁻¹) m * ψ (h * m)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [show -m = (-1 : F) * m by ring, map_mul]
  simp only [MulChar.mul_apply]
  ring

/-- The nonprincipal ramified value at zero frequency is exactly zero. -/
theorem localConvolution_zero (χ ν : MulChar F ℂ) (hχ : χ ≠ 1)
    (hν : ν * χ⁻¹ ≠ 1) (ψ : AddChar F ℂ) :
    localConvolution χ ν ψ 0 = 0 := by
  rw [localConvolution_eq χ ν hχ ψ 0]
  simp only [gaussAt, AddChar.mulShift_zero, gaussSum_one_right hν, mul_zero]

/-- The exceptional principal residue character is not discarded: for a
nonzero primitive frequency its exact value is the negative Gauss factor. -/
theorem localConvolution_same_nonzero (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localConvolution χ χ ψ h = - (χ⁻¹ (-1) * gaussSum χ ψ) := by
  rw [localConvolution_eq χ χ hχ ψ h, mul_inv_cancel]
  have hshift : ψ.mulShift h ≠ 1 := hψ hh
  rw [gaussAt, gaussSum_one_left hshift]
  ring

#print axioms fourier_pullback_eq_zero
#print axioms sum_pullback
#print axioms gauss_norm
#print axioms localConvolution_eq
end FiniteField
end HighBin.FiniteResidueFourier
