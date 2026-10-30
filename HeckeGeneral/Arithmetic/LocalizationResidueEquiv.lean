import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Residue rings unchanged by inverting exterior units

Mathlib's actual quotient-localization instance and its localization-at-units
equivalence identify the original residue ring with the extended-ideal
quotient. The map on every ordinary integer is the literal quotient map.
This applies to general ideals and requires no principal-ideal-domain
assumption. Denominator invertibility remains an explicit algebraic condition.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open scoped Classical

variable {R : Type*} [CommRing R]
variable (M : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
variable [IsLocalization M A]

/-- The actual quotient before and after localization, when every denominator
is already invertible modulo the given ideal. -/
def localizationResidueEquiv (I : Ideal R)
    (hunits : ∀ m : M, IsUnit (Ideal.Quotient.mk I m.val)) :
    (R ⧸ I) ≃+* (A ⧸ I.map (algebraMap R A)) :=
  (IsLocalization.atUnits (R ⧸ I) (Algebra.algebraMapSubmonoid (R ⧸ I) M)
    (S := A ⧸ I.map (algebraMap R A)) (by
      rintro _ ⟨m, hm, rfl⟩
      exact hunits ⟨m, hm⟩)).toRingEquiv

@[simp] theorem localizationResidueEquiv_mk (I : Ideal R)
    (hunits : ∀ m : M, IsUnit (Ideal.Quotient.mk I m.val)) (r : R) :
    localizationResidueEquiv M A I hunits (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A r) := rfl

@[simp] theorem localizationResidueEquiv_symm_mk (I : Ideal R)
    (hunits : ∀ m : M, IsUnit (Ideal.Quotient.mk I m.val)) (r : R) :
    (localizationResidueEquiv M A I hunits).symm
        (Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A r)) =
      Ideal.Quotient.mk I r := by
  apply (localizationResidueEquiv M A I hunits).injective
  rw [RingEquiv.apply_symm_apply, localizationResidueEquiv_mk]

theorem finite_localizationResidue (I : Ideal R)
    (hunits : ∀ m : M, IsUnit (Ideal.Quotient.mk I m.val)) [Finite (R ⧸ I)] :
    Finite (A ⧸ I.map (algebraMap R A)) :=
  Finite.of_surjective (localizationResidueEquiv M A I hunits)
    (localizationResidueEquiv M A I hunits).surjective

theorem card_localizationResidue (I : Ideal R)
    (hunits : ∀ m : M, IsUnit (Ideal.Quotient.mk I m.val)) :
    Nat.card (A ⧸ I.map (algebraMap R A)) = Nat.card (R ⧸ I) :=
  Nat.card_congr (localizationResidueEquiv M A I hunits).symm.toEquiv

section Away

variable (a : R) [IsLocalization.Away a A]

omit [IsLocalization M A] in
/-- A denominator coprime to the ideal is a genuine unit in its residue ring. -/
theorem isUnit_quotient_of_sup_span_eq_top (I : Ideal R)
    (hcoprime : I ⊔ Ideal.span ({a} : Set R) = ⊤) :
    IsUnit (Ideal.Quotient.mk I a) := by
  apply Ideal.span_singleton_eq_top.mp
  have h := congrArg (Ideal.map (Ideal.Quotient.mk I)) hcoprime
  simpa only [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    Ideal.map_span, Set.image_singleton, Ideal.map_top] using h

omit [IsLocalization M A] in
/-- Inverting one element coprime to the modulus preserves its actual residue ring. -/
def awayResidueEquiv (I : Ideal R)
    (hcoprime : I ⊔ Ideal.span ({a} : Set R) = ⊤) :
    (R ⧸ I) ≃+* (A ⧸ I.map (algebraMap R A)) :=
  localizationResidueEquiv (Submonoid.powers a) A I (by
    rintro ⟨m, n, rfl⟩
    rw [map_pow]
    exact (isUnit_quotient_of_sup_span_eq_top a I hcoprime).pow n)

omit [IsLocalization M A] in
@[simp] theorem awayResidueEquiv_mk (I : Ideal R)
    (hcoprime : I ⊔ Ideal.span ({a} : Set R) = ⊤) (r : R) :
    awayResidueEquiv A a I hcoprime (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A r) := rfl

end Away

end HeckeGeneral.Arithmetic
