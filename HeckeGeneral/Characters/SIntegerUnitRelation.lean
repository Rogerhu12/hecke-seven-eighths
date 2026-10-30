import HeckeGeneral.Characters.LocalResidueCharacter
import HeckeGeneral.Characters.InfiniteComponent
import Mathlib.RingTheory.DedekindDomain.SInteger

/-! Actual Mathlib S-units, their principal idèles, and finite/infinite compatibility.

This file uses `Set.unit` and the existing equivalence
with the units of `Set.integer`; it introduces no replacement S-integer construction.
No finiteness of S, finite-generation theorem, or principal ideal hypothesis is needed.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The existing S-unit subgroup maps into the actual principal idèles. -/
def sUnitPrincipalIdele : S.unit K →* IdeleGroup (𝓞 K) K :=
  (IdeleGroup.unitEmbedding (𝓞 K) K).comp (S.unit K).subtype

/-- Use Mathlib's equivalence to embed units of the actual S-integer ring. -/
def sIntegerUnitPrincipalIdele : (S.integer K)ˣ →* IdeleGroup (𝓞 K) K :=
  (sUnitPrincipalIdele K S).comp (S.unitEquivUnitsInteger K).symm.toMonoidHom

@[simp] theorem sIntegerUnitPrincipalIdele_equiv (u : S.unit K) :
    sIntegerUnitPrincipalIdele K S (S.unitEquivUnitsInteger K u) =
      sUnitPrincipalIdele K S u := by
  simp [sIntegerUnitPrincipalIdele]

/-- A global S-unit regarded as a unit in one actual finite completion. -/
def sUnitLocal (v : HeightOneSpectrum (𝓞 K)) : S.unit K →* (v.adicCompletion K)ˣ :=
  (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom).comp (S.unit K).subtype

/-- Outside S both the element and its inverse are local integers. -/
theorem sUnitLocal_mem_integral (u : S.unit K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S) : sUnitLocal K S v u ∈ (v.adicCompletionIntegers K).units := by
  constructor
  · change (((u : Kˣ) : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
    rw [mem_adicCompletionIntegers]
    rw [adicCompletion.valued_coe]
    exact (Set.unit_valuation_eq_one S K u hv).le
  · change (((u⁻¹ : S.unit K) : Kˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
    rw [mem_adicCompletionIntegers]
    rw [adicCompletion.valued_coe]
    exact (Set.unit_valuation_eq_one S K u⁻¹ hv).le

/-- The actual local integer unit, available exactly at the places outside S. -/
def sUnitLocalInteger (u : S.unit K) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    (LocalIntegerRing K v)ˣ :=
  integerUnitOfLocalUnit K v (sUnitLocal K S v u) (sUnitLocal_mem_integral K S u v hv)

@[simp] theorem sUnitLocalInteger_embedding (u : S.unit K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    localIntegerUnitsEmbedding K v (sUnitLocalInteger K S u v hv) = sUnitLocal K S v u :=
  localIntegerUnitsEmbedding_integerUnitOfLocalUnit K v _ _

theorem sUnitLocal_norm_one (u : S.unit K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S) : ‖(sUnitLocal K S v u).val‖ = 1 :=
  (local_norm_one_iff_integral_unit K v _).mpr (sUnitLocal_mem_integral K S u v hv)

/-- All infinite coordinates of an S-unit. -/
def sUnitArchimedean : S.unit K →* (∀ v : InfinitePlace K, v.Completionˣ) where
  toFun u v := Units.map (algebraMap K v.Completion).toMonoidHom (u : Kˣ)
  map_one' := by funext v; simp
  map_mul' u w := by funext v; simp

/-- The genuine finite principal part, with every infinite coordinate equal to one. -/
def sUnitFiniteIdele : S.unit K →* IdeleGroup (𝓞 K) K :=
  (Units.map ((1 : K →* InfiniteAdeleRing K).prod
    (algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).toMonoidHom)).comp
      (S.unit K).subtype

/-- Split the principal idèle without changing either of its actual coordinate families. -/
theorem sUnitPrincipalIdele_eq_finite_mul_infinite (u : S.unit K) :
    sUnitPrincipalIdele K S u =
      sUnitFiniteIdele K S u * archimedeanIdele K (sUnitArchimedean K S u) := by
  apply Units.ext
  apply Prod.ext
  · funext v
    change algebraMap K v.Completion ((u : Kˣ) : K) =
      1 * algebraMap K v.Completion ((u : Kˣ) : K)
    exact (one_mul _).symm
  · change algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) ((u : Kˣ) : K) =
      algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) ((u : Kˣ) : K) * 1
    exact (mul_one _).symm

def sUnitFiniteCharacter (χ : HeckeCharacter K) : S.unit K →* Circle :=
  (toIdeleCharacter K χ).toMonoidHom.comp (sUnitFiniteIdele K S)

def sUnitInfinityCharacter (χ : HeckeCharacter K) : S.unit K →* Circle where
  toFun u := ∏ v, infiniteComponent K v χ (sUnitArchimedean K S u v)
  map_one' := by simp
  map_mul' u w := by simp [Finset.prod_mul_distrib]

/-- The finite and infinite restrictions satisfy the actual principal-idèle relation. -/
theorem sUnitFinite_mul_infinity_eq_one (χ : HeckeCharacter K) (u : S.unit K) :
    sUnitFiniteCharacter K S χ u * sUnitInfinityCharacter K S χ u = 1 := by
  change toIdeleCharacter K χ (sUnitFiniteIdele K S u) *
    (∏ v, infiniteComponent K v χ (sUnitArchimedean K S u v)) = 1
  rw [← character_archimedeanIdele, ← map_mul,
    ← sUnitPrincipalIdele_eq_finite_mul_infinite]
  exact toIdeleCharacter_trivial K χ (u : Kˣ)

theorem sUnitFinite_eq_infinity_inv (χ : HeckeCharacter K) (u : S.unit K) :
    sUnitFiniteCharacter K S χ u = (sUnitInfinityCharacter K S χ u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (sUnitFinite_mul_infinity_eq_one K S χ u)

end HeckeGeneral.Characters
