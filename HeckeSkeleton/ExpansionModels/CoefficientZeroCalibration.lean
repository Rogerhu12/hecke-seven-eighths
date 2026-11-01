import HeckeGeneral.Analysis.HeckeConjugation
import HeckeGeneral.Characters.UnramifiedPrimeCoefficientAlgebra
import HeckeGeneral.Analysis.FrequencyRowOrbit
import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-!
# Character inversion and products with the original ramified zeros

These are project adapters, not independently compiled Mathlib modules.
Inversion preserves zero coefficients.  Multiplication of character
coefficients is only asserted when the right character is unramified at
all prime divisors of the actual ideal; two ramified characters could have
an unramified product, so that premise must not be silently dropped.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical ComplexConjugate nonZeroDivisors

section Coefficients

variable (K : Type*) [Field K] [NumberField K]

/-- The inverse of a ramified zero is again zero. -/
theorem primeCoefficient_inv_zero_extended (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K χ⁻¹ p = (primeCoefficient K χ p)⁻¹ := by
  rw [primeCoefficient_inv]
  unfold primeCoefficient
  split_ifs with h
  · exact (Circle.coe_inv_eq_conj _).symm
  · simp

section IdealExtension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma primeIdealValue_pointwise_inv (a : HeightOneSpectrum R → ℂ) (P : Ideal R) :
    primeIdealValue (fun p => (a p)⁻¹) P = (primeIdealValue a P)⁻¹ := by
  unfold primeIdealValue
  split_ifs <;> simp

theorem idealCoefficient_pointwise_inv (a : HeightOneSpectrum R → ℂ) (I : Ideal R) :
    idealCoefficient (fun p => (a p)⁻¹) I = (idealCoefficient a I)⁻¹ := by
  by_cases hI : I = ⊥
  · subst I
    simp
  simp only [idealCoefficient, if_neg hI]
  simp_rw [primeIdealValue_pointwise_inv]
  exact Multiset.prod_map_inv

/-- Factorwise multiplication, including zero local factors. -/
theorem idealCoefficient_pointwise_mul (a b : HeightOneSpectrum R → ℂ) (I : Ideal R) :
    idealCoefficient (fun p => a p * b p) I = idealCoefficient a I * idealCoefficient b I := by
  by_cases hI : I = ⊥
  · subst I
    simp
  have hp (P : Ideal R) :
      primeIdealValue (fun p => a p * b p) P = primeIdealValue a P * primeIdealValue b P := by
    unfold primeIdealValue
    split_ifs <;> simp
  simp only [idealCoefficient, if_neg hI]
  simp_rw [hp]
  exact Multiset.prod_map_mul

/-- Equality on the genuine prime divisors suffices for ideal coefficients. -/
theorem idealCoefficient_congr_on_divisors (a b : HeightOneSpectrum R → ℂ)
    (I : Ideal R) (h : ∀ p : HeightOneSpectrum R, p.asIdeal ∣ I → a p = b p) :
    idealCoefficient a I = idealCoefficient b I := by
  by_cases hI : I = ⊥
  · subst I
    simp
  simp only [idealCoefficient, if_neg hI]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hprime := prime_of_normalized_factor P hP
  have hdvd : P ∣ I := dvd_of_mem_normalizedFactors hP
  simpa only [primeIdealValue, dif_pos hprime] using h (HeightOneSpectrum.ofPrime hprime) hdvd

end IdealExtension

theorem heckeIdealCoefficient_inv_zero_extended (χ : HeckeCharacter K)
    (I : NonzeroIdeal K) :
    heckeIdealCoefficient K χ⁻¹ I = (heckeIdealCoefficient K χ I)⁻¹ := by
  have hp : primeCoefficient K χ⁻¹ = fun p => (primeCoefficient K χ p)⁻¹ :=
    funext (primeCoefficient_inv_zero_extended K χ)
  unfold heckeIdealCoefficient nonzeroIdealCoefficient
  rw [hp]
  exact idealCoefficient_pointwise_inv _ _

theorem heckeIdealCoefficient_signed_power (χ : HeckeCharacter K)
    (I : NonzeroIdeal K) (e : ℤ) (he : e = -1 ∨ e = 1) :
    heckeIdealCoefficient K (χ ^ e) I = (heckeIdealCoefficient K χ I) ^ e := by
  rcases he with rfl | rfl
  · simpa using heckeIdealCoefficient_inv_zero_extended K χ I
  · simp

/-- The precise multiplicativity premise required before background and
row characters can be combined into the deleted-L coefficient. -/
theorem heckeIdealCoefficient_mul_right_unramified_on_divisors
    (ψ χ : HeckeCharacter K) (I : NonzeroIdeal K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p) :
    heckeIdealCoefficient K (ψ * χ) I =
      heckeIdealCoefficient K ψ I * heckeIdealCoefficient K χ I := by
  unfold heckeIdealCoefficient nonzeroIdealCoefficient
  rw [← idealCoefficient_pointwise_mul]
  apply idealCoefficient_congr_on_divisors
  intro p hp
  exact primeCoefficient_mul_right_unramified K ψ χ p (hχ p hp)

/-- For direction -1 or +1 the signed row coefficient is exactly that of
the signed character, and original zeros are preserved. -/
theorem heckeIdealCoefficient_background_signed
    (ψ χ : HeckeCharacter K) (I : NonzeroIdeal K) (e : ℤ)
    (he : e = -1 ∨ e = 1)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K χ p) :
    heckeIdealCoefficient K (ψ * χ ^ e) I =
      heckeIdealCoefficient K ψ I * (heckeIdealCoefficient K χ I) ^ e := by
  have hpow : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val →
      UnramifiedAt K (χ ^ e) p := by
    intro p hp
    rcases he with rfl | rfl
    · simpa using (hχ p hp).inv K
    · simpa using hχ p hp
  rw [heckeIdealCoefficient_mul_right_unramified_on_divisors K ψ (χ ^ e) I hpow,
    heckeIdealCoefficient_signed_power K χ I e he]


/-- Nonzero whole-ideal coefficient forces unramifiedness at every
actual prime divisor.  This uses the existing zero extension and actual
ideal factorization, without a conductor assumption. -/
theorem unramified_at_divisors_of_coefficient_ne_zero
    (χ : HeckeCharacter K) (I : NonzeroIdeal K)
    (hI : heckeIdealCoefficient K χ I ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I.val) :
    UnramifiedAt K χ p := by
  by_contra hram
  obtain ⟨J, hJ⟩ := hp
  change idealCoefficient (primeCoefficient K χ) I.val ≠ 0 at hI
  rw [hJ, idealCoefficient_mul, idealCoefficient_prime,
    primeCoefficient_of_ramified K χ p hram, zero_mul] at hI
  exact hI rfl

end Coefficients

open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- The supplied row-character calibration itself proves unramifiedness
where the original mask survives.  No extra arithmetic input is added. -/
theorem rowCharacter_unramified_on_masked_divisors
    (u : FrequencyRow K S) (I : NonzeroIdeal K)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)
    (hcop : IsCoprime I.val u.ideal.val.val) :
    ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K (R.character u) p := by
  let E : ExteriorIdeal K S := ⟨I, hS⟩
  have hcal : heckeIdealCoefficient K (R.character u) I =
      idealSymbol K S P.arithmetic E (frequencyRowElement K S P u) := by
    have hc := R.coefficient_calibration u E
    change (if IsCoprime I.val u.ideal.val.val then
      heckeIdealCoefficient K (R.character u) I else 0) =
      idealSymbol K S P.arithmetic E (frequencyRowElement K S P u) at hc
    simpa only [if_pos hcop] using hc
  have hcop' : IsCoprime I.val
      (sIntegerModulusContraction K S (frequencyRowElement K S P u)) := by
    rw [frequencyRowElement_contraction]
    exact hcop
  have hgood := (sIntegerSextic_no_badPrime_iff_coprime_contraction K S I.val
    (nonZeroDivisors.coe_ne_zero I) hS (frequencyRowElement K S P u)).mpr hcop'
  have hn : ‖heckeIdealCoefficient K (R.character u) I‖ = 1 := by
    rw [hcal]
    exact norm_sIntegerSexticIdealEvaluation_eq_one K S P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding I.val
      (nonZeroDivisors.coe_ne_zero I) hS
      (fun p hp => P.arithmetic.away_six p (hS p hp))
      (frequencyRowElement K S P u) hgood
  have hne : heckeIdealCoefficient K (R.character u) I ≠ 0 := by
    intro h
    simpa [h] using hn
  exact unramified_at_divisors_of_coefficient_ne_zero K (R.character u) I hne

/-- Literal inverse-background multiplication after retaining the original
fixed-S/6/coprimality mask, for both signs and with every zero preserved. -/
theorem masked_background_signed_coefficient
    (u : FrequencyRow K S) (I : NonzeroIdeal K) (ψ : HeckeCharacter K)
    (e : ℤ) (he : e = -1 ∨ e = 1) :
    (heckeIdealCoefficient K ψ I * (heckeIdealCoefficient K (R.character u) I) ^ e) *
        (if completeIdealCommonMask K S u.ideal.val I.val then (1 : ℂ) else 0) =
      heckeIdealCoefficient K (ψ * R.character u ^ e) I *
        (if completeIdealCommonMask K S u.ideal.val I.val then (1 : ℂ) else 0) := by
  by_cases h : (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val →
      p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧ IsCoprime I.val u.ideal.val.val
  · rw [heckeIdealCoefficient_background_signed K ψ (R.character u) I e he
      (rowCharacter_unramified_on_masked_divisors K S P R u I
        (fun p hp => (h.1 p hp).1) h.2)]
  · simp [completeIdealCommonMask, h]

end HeckeGeneral.Analysis.ExpansionRecipe

#print axioms HeckeGeneral.Analysis.ExpansionRecipe.rowCharacter_unramified_on_masked_divisors
#print axioms HeckeGeneral.Analysis.ExpansionRecipe.masked_background_signed_coefficient
