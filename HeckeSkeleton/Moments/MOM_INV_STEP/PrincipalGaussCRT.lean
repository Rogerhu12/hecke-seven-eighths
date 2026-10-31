import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Signed CRT factorization with the literal principal additive phases

The cofactor map is constructed from the proved ideal CRT and quotient
units. Its value is literally c₂a+c₁b. Thus the product-modulus phase is
the product of the two actual e(a/c₁), e(b/c₂) phases. The two cross-character
factors remain in the finite Gauss identity. This is valid for unit
conductors as well as nontrivial conductors.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalGaussCRT

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical BigOperators

abbrev QuotientRing (R : Type*) [CommRing R] (c : R) :=
  R ⧸ Ideal.span ({c} : Set R)

section Ring

variable {R : Type*} [CommRing R]
variable (c₁ c₂ : R) (hcop : IsCoprime c₁ c₂)

/-- The ordinary CRT, on the actual product of principal moduli. -/
def quotientCRT : QuotientRing R (c₁ * c₂) ≃+*
    QuotientRing R c₁ × QuotientRing R c₂ :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton c₁ c₂).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _
      ((Ideal.isCoprime_span_singleton_iff c₁ c₂).mpr hcop))

@[simp] theorem quotientCRT_mk (a : R) :
    quotientCRT c₁ c₂ hcop (Ideal.Quotient.mk _ a) =
      (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ a) := by
  apply Prod.ext <;>
    simp only [quotientCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      Ideal.quotientMulEquivQuotientProd_fst, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]

private theorem firstCofactor_isUnit :
    IsUnit (Ideal.Quotient.mk (Ideal.span ({c₁} : Set R)) c₂) := by
  have h := hcop.map (Ideal.Quotient.mk (Ideal.span ({c₁} : Set R)))
  rw [Ideal.Quotient.mk_singleton_self] at h
  exact isCoprime_zero_left.mp h

private theorem secondCofactor_isUnit :
    IsUnit (Ideal.Quotient.mk (Ideal.span ({c₂} : Set R)) c₁) :=
  firstCofactor_isUnit c₂ c₁ hcop.symm

/-- The cofactor form of CRT; no arbitrary inverse representative occurs. -/
def cofactorCRT : QuotientRing R c₁ × QuotientRing R c₂ ≃
    QuotientRing R (c₁ * c₂) :=
  (Equiv.prodCongr (firstCofactor_isUnit c₁ c₂ hcop).unit.mulLeft
    (secondCofactor_isUnit c₁ c₂ hcop).unit.mulLeft).trans
      (quotientCRT c₁ c₂ hcop).symm.toEquiv

theorem quotientCRT_cofactorCRT (x : QuotientRing R c₁ × QuotientRing R c₂) :
    quotientCRT c₁ c₂ hcop (cofactorCRT c₁ c₂ hcop x) =
      (Ideal.Quotient.mk _ c₂ * x.1, Ideal.Quotient.mk _ c₁ * x.2) := by
  change quotientCRT c₁ c₂ hcop ((quotientCRT c₁ c₂ hcop).symm
    (((firstCofactor_isUnit c₁ c₂ hcop).unit : QuotientRing R c₁) * x.1,
      ((secondCofactor_isUnit c₁ c₂ hcop).unit : QuotientRing R c₂) * x.2)) = _
  rw [RingEquiv.apply_symm_apply, IsUnit.unit_spec, IsUnit.unit_spec]

@[simp] theorem cofactorCRT_mk (a b : R) :
    cofactorCRT c₁ c₂ hcop (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (c₂ * a + c₁ * b) := by
  apply (quotientCRT c₁ c₂ hcop).injective
  rw [quotientCRT_cofactorCRT, quotientCRT_mk]
  apply Prod.ext <;>
    simp only [map_add, map_mul, Ideal.Quotient.mk_singleton_self,
      zero_mul, mul_zero, zero_add, add_zero]

/-- Product character on the literal product-modulus quotient. A monoid
hom is used so the unit conductor has its correct constant coefficient. -/
def compositeCharacter (χ₁ : QuotientRing R c₁ →* ℂ)
    (χ₂ : QuotientRing R c₂ →* ℂ) : QuotientRing R (c₁ * c₂) →* ℂ where
  toFun a := χ₁ (quotientCRT c₁ c₂ hcop a).1 * χ₂ (quotientCRT c₁ c₂ hcop a).2
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Prod.fst_mul, Prod.snd_mul]
    ring

theorem compositeCharacter_cofactorCRT (χ₁ : QuotientRing R c₁ →* ℂ)
    (χ₂ : QuotientRing R c₂ →* ℂ) (x : QuotientRing R c₁ × QuotientRing R c₂) :
    compositeCharacter c₁ c₂ hcop χ₁ χ₂ (cofactorCRT c₁ c₂ hcop x) =
      (χ₁ (Ideal.Quotient.mk _ c₂) * χ₂ (Ideal.Quotient.mk _ c₁)) *
        (χ₁ x.1 * χ₂ x.2) := by
  change χ₁ (quotientCRT c₁ c₂ hcop (cofactorCRT c₁ c₂ hcop x)).1 *
    χ₂ (quotientCRT c₁ c₂ hcop (cofactorCRT c₁ c₂ hcop x)).2 = _
  rw [quotientCRT_cofactorCRT]
  simp only [map_mul]
  ring

end Ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => Set.integer S K
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → localDifferentExponent K p = 0)
variable (c₁ c₂ : OS) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hcop : IsCoprime c₁ c₂)

/-- The actual product principal phase splits under the constructed
cofactor CRT. This is a proved finite character identity. -/
theorem principalCharacter_cofactorCRT
    (x : QuotientRing OS c₁ × QuotientRing OS c₂) :
    sIntegerActualModulusAddCharacter K S hS (c₁ * c₂) (mul_ne_zero hc₁ hc₂)
        (cofactorCRT c₁ c₂ hcop x) =
      sIntegerActualModulusAddCharacter K S hS c₁ hc₁ x.1 *
        sIntegerActualModulusAddCharacter K S hS c₂ hc₂ x.2 := by
  rcases x with ⟨x, y⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h₁ : (c₁ : K) ≠ 0 := fun h => hc₁ (Subtype.ext h)
  have h₂ : (c₂ : K) ≠ 0 := fun h => hc₂ (Subtype.ext h)
  rw [cofactorCRT_mk, map_add, AddChar.map_add_eq_mul]
  congr 1
  · rw [sIntegerActualModulusAddCharacter_mk, sIntegerActualModulusAddCharacter_mk]
    congr 1
    change ((c₂ : K) * (a : K)) / ((c₁ : K) * (c₂ : K)) = (a : K) / (c₁ : K)
    field_simp [h₁, h₂] <;> ring
  · rw [sIntegerActualModulusAddCharacter_mk, sIntegerActualModulusAddCharacter_mk]
    congr 1
    change ((c₁ : K) * (b : K)) / ((c₁ : K) * (c₂ : K)) = (b : K) / (c₂ : K)
    field_simp [h₁, h₂] <;> ring

/-- Actual finite unnormalized principal Gauss sum for a multiplicative
quotient coefficient, with the source modulus and literal phase shown. -/
def principalGauss (c : OS) (hc : c ≠ 0) (χ : QuotientRing OS c →* ℂ) : ℂ := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (QuotientRing OS c)
  exact ∑ a : QuotientRing OS c, χ a * sIntegerActualModulusAddCharacter K S hS c hc a

/-- Signed CRT factorization. Both cross factors are retained before
absolute values, and every quotient class is included. -/
theorem principalGauss_mul (χ₁ : QuotientRing OS c₁ →* ℂ)
    (χ₂ : QuotientRing OS c₂ →* ℂ) :
    principalGauss K S hS (c₁ * c₂) (mul_ne_zero hc₁ hc₂)
      (compositeCharacter c₁ c₂ hcop χ₁ χ₂) =
      (χ₁ (Ideal.Quotient.mk _ c₂) * χ₂ (Ideal.Quotient.mk _ c₁)) *
        principalGauss K S hS c₁ hc₁ χ₁ * principalGauss K S hS c₂ hc₂ χ₂ := by
  letI := finite_sIntegerPrincipalResidue K S c₁ hc₁
  letI := Fintype.ofFinite (QuotientRing OS c₁)
  letI := finite_sIntegerPrincipalResidue K S c₂ hc₂
  letI := Fintype.ofFinite (QuotientRing OS c₂)
  letI := finite_sIntegerPrincipalResidue K S (c₁ * c₂) (mul_ne_zero hc₁ hc₂)
  letI := Fintype.ofFinite (QuotientRing OS (c₁ * c₂))
  unfold principalGauss
  have hs := (cofactorCRT c₁ c₂ hcop).sum_comp
    (fun z : QuotientRing OS (c₁ * c₂) => compositeCharacter c₁ c₂ hcop χ₁ χ₂ z *
      sIntegerActualModulusAddCharacter K S hS (c₁ * c₂) (mul_ne_zero hc₁ hc₂) z)
  rw [← hs]
  have hterm (x : QuotientRing OS c₁ × QuotientRing OS c₂) :
      compositeCharacter c₁ c₂ hcop χ₁ χ₂ (cofactorCRT c₁ c₂ hcop x) *
        sIntegerActualModulusAddCharacter K S hS (c₁ * c₂) (mul_ne_zero hc₁ hc₂)
          (cofactorCRT c₁ c₂ hcop x) =
      (χ₁ (Ideal.Quotient.mk _ c₂) * χ₂ (Ideal.Quotient.mk _ c₁)) *
        ((χ₁ x.1 * sIntegerActualModulusAddCharacter K S hS c₁ hc₁ x.1) *
          (χ₂ x.2 * sIntegerActualModulusAddCharacter K S hS c₂ hc₂ x.2)) := by
    rw [compositeCharacter_cofactorCRT, principalCharacter_cofactorCRT K S hS c₁ c₂ hc₁ hc₂ hcop]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalGaussCRT
