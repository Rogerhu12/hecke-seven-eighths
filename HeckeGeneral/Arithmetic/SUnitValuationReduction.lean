import HeckeGeneral.Arithmetic.SUnitPrimePowers
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval

/-!
# Finite valuation reduction by actual S-units

Products of the prime-power S-units realize every class-number multiple of a
valuation vector. Euclidean division then reduces every integral valuation
vector to a fixed finite box. This is the finite-place step of constructing
compact representatives; no S-unit finite-generation theorem is assumed.

The native build and all-origin declaration audit are recorded in
`.cache/lattice-mask-audit.log` (138 declarations across six modules).
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def sUnitCoordinateProduct (a : S → ℤ) : S.unit K :=
  ∏ v : S, (sUnitPrimePower K S v.val v.property) ^ a v

theorem sUnitCoordinateProduct_valuation (a : S → ℤ) (w : S) :
    sUnitValuations K S (sUnitCoordinateProduct K S a) w =
      Multiplicative.ofAdd (-(classNumber K : ℤ)) ^ a w := by
  simp [sUnitCoordinateProduct, map_prod, Finset.prod_apply,
    sUnitValuations_primePower, ite_pow]

/-- Every integer multiple of the class number is realized by an actual S-unit. -/
theorem exists_sUnit_valuation_multiple (a : S → ℤ) :
    ∃ u : S.unit K, ∀ w : S,
      (sUnitValuations K S u w).toAdd = -(classNumber K : ℤ) * a w := by
  refine ⟨sUnitCoordinateProduct K S a, fun w => ?_⟩
  rw [sUnitCoordinateProduct_valuation, toAdd_zpow]
  simp [mul_comm]

/-- A fixed finite box meets every translate of the actual S-unit valuation image. -/
theorem exists_sUnit_valuation_reduction (t : S → ℤ) :
    ∃ u : S.unit K, ∀ w : S,
      t w + (sUnitValuations K S u w).toAdd = t w % (classNumber K : ℤ) := by
  obtain ⟨u, hu⟩ := exists_sUnit_valuation_multiple K S
    (fun w => t w / (classNumber K : ℤ))
  refine ⟨u, fun w => ?_⟩
  rw [hu w]
  have h := Int.emod_add_mul_ediv (t w) (classNumber K : ℤ)
  linarith

theorem exists_sUnit_valuation_in_box (t : S → ℤ) :
    ∃ u : S.unit K, ∀ w : S,
      0 ≤ t w + (sUnitValuations K S u w).toAdd ∧
      t w + (sUnitValuations K S u w).toAdd < (classNumber K : ℤ) := by
  obtain ⟨u, hu⟩ := exists_sUnit_valuation_reduction K S t
  have hh : (0 : ℤ) < classNumber K := by exact_mod_cast classNumber_pos K
  refine ⟨u, fun w => ?_⟩
  rw [hu w]
  exact ⟨Int.emod_nonneg _ hh.ne', Int.emod_lt_of_pos _ hh⟩

end HeckeGeneral.Arithmetic
