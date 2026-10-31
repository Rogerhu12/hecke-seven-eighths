import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Extension
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Choosing the complex embedding before the arithmetic context

The KP coefficient embedding sends the chosen sixth root to
`exp (2 * pi * I / 6)`.  An arbitrary complex embedding need not have
this property.  Here the primitive twelfth root is prescribed first,
and the field embedding is chosen to send it to the standard twelfth
root.  Squaring gives exactly the sixth-root convention used by KP.

The existence proof extends a rational embedding through the minimal
polynomial of the prescribed primitive root.  It uses no theta input.
The project adapter makes its one arithmetic choice only after fixing
this embedding, so the same finite set and the same generator context
can subsequently be used by the global source.
-/

noncomputable section

open Polynomial

namespace ThetaGlobal.GlobalEmbedding

def canonicalTwelfthRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12)

def canonicalSixthRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)

theorem canonicalTwelfthRoot_primitive : IsPrimitiveRoot canonicalTwelfthRoot 12 :=
  Complex.isPrimitiveRoot_exp 12 (by norm_num)

theorem canonicalSixthRoot_primitive : IsPrimitiveRoot canonicalSixthRoot 6 :=
  Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem canonicalTwelfthRoot_sq : canonicalTwelfthRoot ^ 2 = canonicalSixthRoot := by
  unfold canonicalTwelfthRoot canonicalSixthRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

variable {F : Type*} [Field F] [NumberField F]

/-- A prescribed primitive twelfth root can be sent to the canonical
complex root by an embedding of the whole number field. -/
theorem exists_alignedEmbedding (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    ∃ σ : F →+* ℂ, σ ζ = canonicalTwelfthRoot := by
  have hmin : minpoly ℚ ζ = cyclotomic 12 ℚ :=
    (cyclotomic_eq_minpoly_rat hζ (by norm_num)).symm
  have hroot : aeval canonicalTwelfthRoot (minpoly ℚ ζ) = 0 := by
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic,
      ← IsRoot.def, isRoot_cyclotomic_iff]
    exact canonicalTwelfthRoot_primitive
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_adjoin_splits_of_aeval
    (F := ℚ) (E := F) (K := ℂ) (S := Set.univ) (x := ζ)
    (y := canonicalTwelfthRoot)
    (fun s _ => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    (IntermediateField.adjoin_univ ℚ F) hroot
  exact ⟨φ.toRingHom, hφ⟩

/-- Fix this embedding before making the final arithmetic choice. -/
def alignedEmbedding (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : F →+* ℂ :=
  Classical.choose (exists_alignedEmbedding ζ hζ)

@[simp] theorem alignedEmbedding_root12 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    alignedEmbedding ζ hζ ζ = canonicalTwelfthRoot :=
  Classical.choose_spec (exists_alignedEmbedding ζ hζ)

@[simp] theorem alignedEmbedding_root6 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    alignedEmbedding ζ hζ (ζ ^ 2) = canonicalSixthRoot := by
  rw [map_pow, alignedEmbedding_root12, canonicalTwelfthRoot_sq]

@[simp] theorem alignedEmbedding_root6_pow (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (i : ℕ) :
    alignedEmbedding ζ hζ ((ζ ^ 2) ^ i) = canonicalSixthRoot ^ i := by
  rw [map_pow, alignedEmbedding_root6]

/-- The compatibility statement is independent of the choice of an
exponent representing the sixth root. -/
theorem alignedEmbedding_of_sixth_power (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : F) (i : ℕ) (hi : (ζ ^ 2) ^ i = z) :
    alignedEmbedding ζ hζ z = canonicalSixthRoot ^ i := by
  rw [← hi, alignedEmbedding_root6_pow]

/-- Every sixth root has the exponent required to compare with the KP
coefficient convention. -/
theorem sixthRoot_exponent (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : rootsOfUnity 6 F) :
    ∃ i : ℕ, i < 6 ∧ (ζ ^ 2) ^ i = ((z : Fˣ) : F) := by
  have h6 : IsPrimitiveRoot (ζ ^ 2) 6 := hζ.pow (by norm_num) (by norm_num)
  apply h6.eq_pow_of_pow_eq_one
  exact congrArg (fun a : Fˣ => (a : F)) z.property

theorem alignedEmbedding_sixthRoot (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : rootsOfUnity 6 F) :
    ∃ i : ℕ, i < 6 ∧
      alignedEmbedding ζ hζ ((z : Fˣ) : F) = canonicalSixthRoot ^ i := by
  obtain ⟨i, hi, hz⟩ := sixthRoot_exponent ζ hζ z
  exact ⟨i, hi, alignedEmbedding_of_sixth_power ζ hζ _ i hz⟩

end ThetaGlobal.GlobalEmbedding
