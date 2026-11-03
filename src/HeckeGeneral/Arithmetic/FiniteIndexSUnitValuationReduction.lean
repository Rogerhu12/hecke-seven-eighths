import HeckeGeneral.Arithmetic.SUnitValuationReduction
import Mathlib.GroupTheory.OrderOfElement

/-!
Finite-place valuation reduction by actual elements of a finite-index S-unit
subgroup. The class number and subgroup index give the box width. No
principal-ideal-domain or S-unit finite-generation assumption is introduced.
Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def finiteIndexSUnitBoxWidth (Γ : Subgroup (S.unit K)) : ℕ :=
  classNumber K * Γ.index

omit [Fintype S] in
theorem finiteIndexSUnitBoxWidth_pos (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    0 < finiteIndexSUnitBoxWidth K S Γ := by
  exact Nat.mul_pos (classNumber_pos K)
    (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Γ)))

/-- The constructed element belongs to the actual subgroup by its index power. -/
def finiteIndexSUnitCoordinateProduct (Γ : Subgroup (S.unit K)) (a : S → ℤ) : Γ :=
  ⟨sUnitCoordinateProduct K S a ^ Γ.index,
    Γ.pow_index_mem (sUnitCoordinateProduct K S a)⟩

/-- The valuation image contains every negative box-width multiple of an
integer vector, with the displayed product as its genuine subgroup witness. -/
theorem finiteIndexSUnitCoordinateProduct_valuation (Γ : Subgroup (S.unit K))
    (a : S → ℤ) (w : S) :
    (sUnitValuations K S (finiteIndexSUnitCoordinateProduct K S Γ a : S.unit K) w).toAdd =
      -(finiteIndexSUnitBoxWidth K S Γ : ℤ) * a w := by
  change (sUnitValuations K S (sUnitCoordinateProduct K S a ^ Γ.index) w).toAdd = _
  rw [map_pow, Pi.pow_apply, toAdd_pow, sUnitCoordinateProduct_valuation, toAdd_zpow]
  simp only [toAdd_ofAdd, nsmul_eq_mul, zsmul_eq_mul,
    finiteIndexSUnitBoxWidth, Nat.cast_mul, Int.cast_id]
  ring

/-- Every integral valuation vector is reduced modulo the fixed positive width
by an actual subgroup element, rather than by an abstract image vector. -/
theorem exists_subgroup_sUnit_valuation_reduction (Γ : Subgroup (S.unit K))
    [Γ.FiniteIndex] (t : S → ℤ) :
    ∃ u : Γ, ∀ w : S,
      t w + (sUnitValuations K S (u : S.unit K) w).toAdd =
        t w % (finiteIndexSUnitBoxWidth K S Γ : ℤ) := by
  refine ⟨finiteIndexSUnitCoordinateProduct K S Γ
    (fun w => t w / (finiteIndexSUnitBoxWidth K S Γ : ℤ)), fun w => ?_⟩
  rw [finiteIndexSUnitCoordinateProduct_valuation]
  have h := Int.emod_add_mul_ediv (t w) (finiteIndexSUnitBoxWidth K S Γ : ℤ)
  linarith

theorem exists_subgroup_sUnit_valuation_in_box (Γ : Subgroup (S.unit K))
    [Γ.FiniteIndex] (t : S → ℤ) :
    ∃ u : Γ, ∀ w : S,
      0 ≤ t w + (sUnitValuations K S (u : S.unit K) w).toAdd ∧
      t w + (sUnitValuations K S (u : S.unit K) w).toAdd <
        (finiteIndexSUnitBoxWidth K S Γ : ℤ) := by
  obtain ⟨u, hu⟩ := exists_subgroup_sUnit_valuation_reduction K S Γ t
  have hh : (0 : ℤ) < finiteIndexSUnitBoxWidth K S Γ := by
    exact_mod_cast finiteIndexSUnitBoxWidth_pos K S Γ
  refine ⟨u, fun w => ?_⟩
  rw [hu w]
  exact ⟨Int.emod_nonneg _ hh.ne', Int.emod_lt_of_pos _ hh⟩

end HeckeGeneral.Arithmetic
