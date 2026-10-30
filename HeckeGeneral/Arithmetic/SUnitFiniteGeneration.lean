import TauCetiReuse.RingTheory.DedekindDomain.SInteger.Unit
import HeckeGeneral.Arithmetic.SUnitValuationReduction
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Finite generation and finite-index valuation image for the actual S-units

Tau Ceti's kernel/extension proof is applied to Mathlib's actual number-field
units. The map is identified with the one used in our explicit finite-box
reduction. Thus finite generation and finite-index power subgroups introduce
no new arithmetic hypotheses on the field.

SOURCE STATUS: native build and complete five-declaration origin audit passed
under Lean 4.34.1; only propext, Classical.choice, and Quot.sound were used.
The four Tau Ceti dependency modules separately passed their complete
25-declaration origin audit. No S-unit rank or quotient compactness is asserted.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem sUnitValuations_eq_unitValuation :
    sUnitValuations K S = Set.unitValuation S K := by
  ext u v
  rfl

theorem sUnitValuations_ker :
    (sUnitValuations K S).ker =
      ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K).subgroupOf (S.unit K) := by
  rw [sUnitValuations_eq_unitValuation]
  exact Set.unitValuation_ker S K

theorem sUnits_finitelyGenerated [Finite S] : Group.FG (S.unit K) := inferInstance

theorem sUnit_power_range_finiteIndex [Finite S] (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom n : S.unit K →* S.unit K).range.FiniteIndex :=
  Subgroup.finiteIndex_range_powMonoidHom_of_fg (S.unit K) hn

/-- The finite-box construction gives the actual finite-index valuation lattice. -/
theorem sUnitValuations_range_finiteIndex [Finite S] :
    (sUnitValuations K S).range.FiniteIndex := by
  let := Fintype.ofFinite S
  have : (powMonoidHom (classNumber K) :
      (S → Multiplicative ℤ) →* (S → Multiplicative ℤ)).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ (classNumber_ne_zero K)
  apply Subgroup.finiteIndex_of_le (H := (powMonoidHom (classNumber K) :
    (S → Multiplicative ℤ) →* (S → Multiplicative ℤ)).range)
  rintro _ ⟨f, rfl⟩
  obtain ⟨u, hu⟩ := exists_sUnit_valuation_multiple K S (fun v => -(f v).toAdd)
  refine ⟨u, ?_⟩
  funext v
  apply Multiplicative.toAdd.injective
  simpa only [powMonoidHom_apply, Pi.pow_apply, Int.toAdd_pow, neg_mul_neg, mul_comm] using hu v

end HeckeGeneral.Arithmetic
