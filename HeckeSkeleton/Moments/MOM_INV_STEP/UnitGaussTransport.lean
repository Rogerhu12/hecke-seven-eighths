import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalGaussCRT

/-!
# Actual Gauss sums under a change of principal generator

The numerator is multiplied by the same unit as the modulus. This is an
explicit bijection of the genuine finite quotients, so the literal
principal additive phase is unchanged. The multiplicative coefficient
contributes its actual value on that unit. For the primitive sextic packet
this value is one on every sixth power of an S-unit.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.UnitGaussTransport

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open PrincipalGaussCRT
open scoped Classical BigOperators

section Ring

variable {R : Type*} [CommRing R]
variable (c : R) (u : Rˣ)

/-- The same ideal, presented by two unit-related generators. -/
def unitQuotient : QuotientRing R (u.val * c) ≃+* QuotientRing R c :=
  Ideal.quotEquivOfEq (Ideal.span_singleton_mul_left_unit u.isUnit c)

@[simp] theorem unitQuotient_mk (a : R) :
    unitQuotient c u (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
  Ideal.quotEquivOfEq_mk _ a

/-- Multiply the numerator and denominator by the same actual unit. -/
def unitNumeratorEquiv : QuotientRing R c ≃ QuotientRing R (u.val * c) :=
  (Units.map (Ideal.Quotient.mk (Ideal.span ({c} : Set R))).toMonoidHom u).mulLeft.trans
    (unitQuotient c u).symm.toEquiv

theorem unitQuotient_unitNumeratorEquiv (x : QuotientRing R c) :
    unitQuotient c u (unitNumeratorEquiv c u x) =
      Ideal.Quotient.mk _ u.val * x := by
  change unitQuotient c u ((unitQuotient c u).symm
    ((Units.map (Ideal.Quotient.mk (Ideal.span ({c} : Set R))).toMonoidHom u :
      QuotientRing R c) * x)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

@[simp] theorem unitNumeratorEquiv_mk (a : R) :
    unitNumeratorEquiv c u (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (u.val * a) := by
  apply (unitQuotient c u).injective
  rw [unitQuotient_unitNumeratorEquiv, unitQuotient_mk, map_mul]

/-- The identical quotient coefficient under the equality of ideals. -/
def unitCharacter (χ : QuotientRing R c →* ℂ) : QuotientRing R (u.val * c) →* ℂ :=
  χ.comp (unitQuotient c u).toMonoidHom

theorem unitCharacter_unitNumeratorEquiv (χ : QuotientRing R c →* ℂ)
    (x : QuotientRing R c) :
    unitCharacter c u χ (unitNumeratorEquiv c u x) =
      χ (Ideal.Quotient.mk _ u.val) * χ x := by
  change χ (unitQuotient c u (unitNumeratorEquiv c u x)) = _
  rw [unitQuotient_unitNumeratorEquiv, map_mul]

end Ring

section Principal

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => Set.integer S K
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → localDifferentExponent K p = 0)
variable (c : OS) (hc : c ≠ 0) (u : OSˣ)

/-- The literal e(a/c) phase is unchanged when both are multiplied by u. -/
theorem principalCharacter_unitNumeratorEquiv (x : QuotientRing OS c) :
    sIntegerActualModulusAddCharacter K S hS (u.val * c) (mul_ne_zero u.ne_zero hc)
        (unitNumeratorEquiv c u x) =
      sIntegerActualModulusAddCharacter K S hS c hc x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hu : (u.val : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hcK : (c : K) ≠ 0 := fun h => hc (Subtype.ext h)
  rw [unitNumeratorEquiv_mk, sIntegerActualModulusAddCharacter_mk,
    sIntegerActualModulusAddCharacter_mk]
  congr 1
  change ((u.val : K) * (a : K)) / ((u.val : K) * (c : K)) = (a : K) / (c : K)
  field_simp [hu, hcK] <;> ring

/-- Exact unit transport for the finite sum, with its unit character
factor retained. No normalized-Gauss or CRT identity is assumed. -/
theorem principalGauss_unit (χ : QuotientRing OS c →* ℂ) :
    principalGauss K S hS (u.val * c) (mul_ne_zero u.ne_zero hc)
        (unitCharacter c u χ) =
      χ (Ideal.Quotient.mk _ u.val) * principalGauss K S hS c hc χ := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (QuotientRing OS c)
  letI := finite_sIntegerPrincipalResidue K S (u.val * c) (mul_ne_zero u.ne_zero hc)
  letI := Fintype.ofFinite (QuotientRing OS (u.val * c))
  unfold principalGauss
  have hs := (unitNumeratorEquiv c u).sum_comp
    (fun z : QuotientRing OS (u.val * c) => unitCharacter c u χ z *
      sIntegerActualModulusAddCharacter K S hS (u.val * c) (mul_ne_zero u.ne_zero hc) z)
  rw [← hs]
  simp_rw [unitCharacter_unitNumeratorEquiv,
    principalCharacter_unitNumeratorEquiv K S hS c hc u, mul_assoc]
  rw [← Finset.mul_sum]

theorem principalGauss_unit_of_value_one (χ : QuotientRing OS c →* ℂ)
    (hχ : χ (Ideal.Quotient.mk _ u.val) = 1) :
    principalGauss K S hS (u.val * c) (mul_ne_zero u.ne_zero hc)
      (unitCharacter c u χ) = principalGauss K S hS c hc χ := by
  rw [principalGauss_unit, hχ, one_mul]

end Principal

end HeckeSkeleton.Moments.MOM_INV_STEP.UnitGaussTransport
