import HeckeGeneral.Characters.ConductorCRT
import HeckeGeneral.Characters.InfiniteComponent

/-! The finite conductor and infinite components agree on actual global integer units. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- The same global integer unit, regarded as an integer unit in each finite completion. -/
def globalIntegerUnitLocalization : (𝓞 K)ˣ →* GlobalIntegralUnits K where
  toFun u v := Units.map (algebraMap (𝓞 K) (LocalIntegerRing K v)).toMonoidHom u
  map_one' := by funext v; exact map_one _
  map_mul' u w := by funext v; exact map_mul _ u w

/-- The embedding of global integer units into the field's multiplicative group. -/
def globalIntegerUnitField : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

/-- All archimedean coordinates of a global integer unit. -/
def globalIntegerUnitArchimedean :
    (𝓞 K)ˣ →* (∀ v : InfinitePlace K, v.Completionˣ) where
  toFun u v := Units.map (algebraMap K v.Completion).toMonoidHom
    (globalIntegerUnitField K u)
  map_one' := by funext v; simp
  map_mul' u w := by funext v; simp

/-- Reduction of an actual global integer unit modulo the actual finite conductor. -/
def conductorGlobalUnitReduction (χ : HeckeCharacter K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ (finiteConductor K χ).val)ˣ :=
  Units.map (Ideal.Quotient.mk (finiteConductor K χ).val).toMonoidHom

theorem conductorGlobalUnitReduction_CRT (χ : HeckeCharacter K) (u : (𝓞 K)ˣ) :
    conductorResidueUnitsCRT K χ (conductorGlobalUnitReduction K χ u) =
      globalConductorReduction K χ (globalIntegerUnitLocalization K u) := by
  funext v
  apply Units.ext
  change conductorResidueCRT K χ (Ideal.Quotient.mk _ u.val) v =
    globalToLocalResidue K v.val (localConductorExponent K χ v.val) u.val
  exact conductorResidueCRT_mk K χ u.val v

/-- The finite character's value on a global unit is its value on the finite integral idèle. -/
theorem conductorUnitCharacter_globalUnit (χ : HeckeCharacter K) (u : (𝓞 K)ˣ) :
    conductorUnitCharacter K χ (conductorGlobalUnitReduction K χ u) =
      globalIntegralComponent K χ (globalIntegerUnitLocalization K u) := by
  have h := conductorUnitCharacter_integral K χ (globalIntegerUnitLocalization K u)
  rw [← conductorGlobalUnitReduction_CRT, MulEquiv.symm_apply_apply] at h
  exact h

/-- A global integer unit's principal idèle is its finite integral part times its infinite part. -/
theorem principalIntegerUnit_eq_finite_mul_infinite (u : (𝓞 K)ˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K (globalIntegerUnitField K u) =
      globalIntegralIdele K (globalIntegerUnitLocalization K u) *
        archimedeanIdele K (globalIntegerUnitArchimedean K u) := by
  apply Units.ext
  apply Prod.ext
  · funext v
    change algebraMap K v.Completion (algebraMap (𝓞 K) K u.val) =
      1 * algebraMap K v.Completion (algebraMap (𝓞 K) K u.val)
    exact (one_mul _).symm
  · apply RestrictedProduct.ext
    intro v
    change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K u.val) =
      ((algebraMap (𝓞 K) (LocalIntegerRing K v) u.val : LocalIntegerRing K v) :
        v.adicCompletion K) * 1
    rw [mul_one]
    rfl

/-- Restrict the entire infinite component to the actual global integer unit group. -/
def globalIntegerUnitInfinityCharacter (χ : HeckeCharacter K) : (𝓞 K)ˣ →* Circle where
  toFun u := ∏ v, infiniteComponent K v χ (globalIntegerUnitArchimedean K u v)
  map_one' := by simp
  map_mul' u w := by simp [Finset.prod_mul_distrib]

theorem globalIntegerUnitInfinityCharacter_eq (χ : HeckeCharacter K) (u : (𝓞 K)ˣ) :
    globalIntegerUnitInfinityCharacter K χ u =
      toIdeleCharacter K χ (archimedeanIdele K (globalIntegerUnitArchimedean K u)) :=
  (character_archimedeanIdele K χ _).symm

/-- The ray-class compatibility condition follows from triviality on principal idèles. -/
theorem conductorUnitCharacter_mul_infinity_eq_one (χ : HeckeCharacter K) (u : (𝓞 K)ˣ) :
    conductorUnitCharacter K χ (conductorGlobalUnitReduction K χ u) *
      globalIntegerUnitInfinityCharacter K χ u = 1 := by
  rw [conductorUnitCharacter_globalUnit, globalIntegerUnitInfinityCharacter_eq]
  change toIdeleCharacter K χ (globalIntegralIdele K (globalIntegerUnitLocalization K u)) *
    toIdeleCharacter K χ (archimedeanIdele K (globalIntegerUnitArchimedean K u)) = 1
  rw [← map_mul, ← principalIntegerUnit_eq_finite_mul_infinite]
  exact toIdeleCharacter_trivial K χ (globalIntegerUnitField K u)

theorem conductorUnitCharacter_eq_infinity_inv (χ : HeckeCharacter K) (u : (𝓞 K)ˣ) :
    conductorUnitCharacter K χ (conductorGlobalUnitReduction K χ u) =
      (globalIntegerUnitInfinityCharacter K χ u)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (conductorUnitCharacter_mul_infinity_eq_one K χ u)

/-- On units congruent to one modulo the conductor, the entire infinite component is trivial. -/
theorem infinityCharacter_trivial_on_conductor_units (χ : HeckeCharacter K) (u : (𝓞 K)ˣ)
    (hu : u.val - 1 ∈ (finiteConductor K χ).val) :
    globalIntegerUnitInfinityCharacter K χ u = 1 := by
  have hred : conductorGlobalUnitReduction K χ u = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk _ u.val = Ideal.Quotient.mk _ 1
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem u.val 1).mpr hu
  have h := conductorUnitCharacter_mul_infinity_eq_one K χ u
  rwa [hred, map_one, one_mul] at h

end HeckeGeneral.Characters
