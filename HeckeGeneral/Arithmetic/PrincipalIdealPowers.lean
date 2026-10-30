import HeckeGeneral.Arithmetic.PrincipalUnitOrbits
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Principal powers for the S-unit valuation construction

The field's actual class number kills every ideal class. In particular,
each nonzero prime ideal has a nonzero generator after taking this one
fixed power. No principal-ideal-domain assumption on the integer ring
is introduced.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField
open scoped nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem ideal_pow_classNumber_isPrincipal (I : Ideal (𝓞 K)) :
    (I ^ classNumber K).IsPrincipal := by
  by_cases hI : I = 0
  · subst I
    rw [zero_pow (classNumber_ne_zero K), Ideal.zero_eq_bot]
    infer_instance
  have hmem : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  apply (ClassGroup.mk0_eq_one_iff (pow_mem hmem (classNumber K))).mp
  have h : ClassGroup.mk0 ((⟨I, hmem⟩ : (Ideal (𝓞 K))⁰) ^ classNumber K) = 1 := by
    rw [map_pow]
    simpa only [classNumber] using (pow_card_eq_one (x := ClassGroup.mk0 ⟨I, hmem⟩))
  exact h

theorem exists_nonzero_generator_classNumber_power (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I ^ classNumber K := by
  let : (I ^ classNumber K).IsPrincipal := ideal_pow_classNumber_isPrincipal K I
  let : NeZero (I ^ classNumber K) := ⟨pow_ne_zero _ hI⟩
  let a := chosenPrincipalGenerator (I ^ classNumber K)
  exact ⟨a.val, principalGenerators_ne_zero _ a, a.property⟩

end HeckeGeneral.Arithmetic
