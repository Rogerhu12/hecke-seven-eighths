import HeckeGeneral.Arithmetic.SIntegerModulusCRT
import HeckeGeneral.Arithmetic.SIntegerModulusNorm

/-! The product of the genuine exterior local coset masses equals the inverse
cardinality of the actual S-integer quotient, hence its inverse product norm.
No normalized local Haar measure or principal ordinary ideal is assumed. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (c : S.integer K) (hc : c ≠ 0)

local notation "P" => sIntegerModulusPlaces K S c hc

theorem natCard_sIntegerPrincipalResidue_eq_primeProduct :
    Nat.card (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) = ∏ v : P,
      v.val.asIdeal.absNorm ^ sIntegerModulusPrimeExponents K S c hc v.val := by
  rw [natCard_sIntegerPrincipalResidue K S c hc,
    ← sIntegerModulus_primePower_product K S c hc, map_prod]
  simp only [map_pow]

/-- The normalized local ball masses multiply to the actual reciprocal index. -/
theorem sIntegerModulus_primeMass_eq_inv_natCard :
    (∏ v : P, (v.val.asIdeal.absNorm : ℝ) ^
      (-(sIntegerModulusPrimeExponents K S c hc v.val : ℤ))) =
        (Nat.card (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) : ℝ)⁻¹ := by
  calc
    _ = (∏ v : P, (v.val.asIdeal.absNorm : ℝ) ^
        sIntegerModulusPrimeExponents K S c hc v.val)⁻¹ := by
      simp only [zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
    _ = ((∏ v : P, v.val.asIdeal.absNorm ^
        sIntegerModulusPrimeExponents K S c hc v.val : ℕ) : ℝ)⁻¹ := by
      simp only [Nat.cast_prod, Nat.cast_pow]
    _ = _ := by rw [← natCard_sIntegerPrincipalResidue_eq_primeProduct K S c hc]

theorem sIntegerModulus_primeMass_eq_inv_productNorm :
    (∏ v : P, (v.val.asIdeal.absNorm : ℝ) ^
      (-(sIntegerModulusPrimeExponents K S c hc v.val : ℤ))) =
        (sIntegerElementNorm K S ⟨c, hc⟩).val⁻¹ := by
  rw [sIntegerModulus_primeMass_eq_inv_natCard K S c hc,
    natCard_sIntegerPrincipalResidue_eq_productNorm K S c hc]

/-- The complex form used by the actual Fourier integral. -/
theorem sIntegerModulus_complexPrimeMass_eq_inv_productNorm :
    (∏ v : P, ((v.val.asIdeal.absNorm : ℝ) ^
      (-(sIntegerModulusPrimeExponents K S c hc v.val : ℤ)) : ℂ)) =
        ((sIntegerElementNorm K S ⟨c, hc⟩).val : ℂ)⁻¹ := by
  have h := congrArg Complex.ofReal (sIntegerModulus_primeMass_eq_inv_productNorm K S c hc)
  simpa only [Complex.ofReal_prod, Complex.ofReal_zpow, Complex.ofReal_inv] using h

end HeckeGeneral.Arithmetic
