import HeckeGeneral.Arithmetic.PrincipalUnitOrbits
import HeckeGeneral.Analysis.IdealSummability

/-!
# Counting integral principal-generator sectors

The disjoint union is over actual nonzero integral ideals and actual unit
orbits of their generators. Nonprincipal ideals contribute an empty fiber;
each principal ideal contributes the full subgroup index. The resulting
linear bound concerns integral ideals, before S-integer localization.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open Ideal NumberField Filter Asymptotics
open scoped Classical nonZeroDivisors Topology

variable (K : Type*) [Field K] [NumberField K]

abbrev BoundedNonzeroIdeals (n : ℕ) :=
  {I : (Ideal (𝓞 K))⁰ // absNorm I.val ≤ n}

instance finite_boundedNonzeroIdeals (n : ℕ) : Finite (BoundedNonzeroIdeals K n) :=
  Ideal.finite_setOfPred_absNorm_le₀ n

instance fintype_boundedNonzeroIdeals (n : ℕ) : Fintype (BoundedNonzeroIdeals K n) :=
  Fintype.ofFinite _

instance boundedNonzeroIdeals_neZero (n : ℕ) (I : BoundedNonzeroIdeals K n) :
    NeZero I.val.val := ⟨nonZeroDivisors.coe_ne_zero I.val⟩

/-- All integral generator sectors up to the specified ideal norm. -/
def BoundedGeneratorSectors (Γ : Subgroup (𝓞 K)ˣ) (n : ℕ) :=
  Σ I : BoundedNonzeroIdeals K n, GeneratorOrbits Γ I.val.val

instance finite_boundedGeneratorSectors (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] (n : ℕ) :
    Finite (BoundedGeneratorSectors K Γ n) := by
  unfold BoundedGeneratorSectors
  infer_instance

theorem card_boundedGeneratorSectors (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] (n : ℕ) :
    Nat.card (BoundedGeneratorSectors K Γ n) =
      ∑ I : BoundedNonzeroIdeals K n,
        (if I.val.val.IsPrincipal then Γ.index else 0) := by
  letI := Fintype.ofFinite (BoundedNonzeroIdeals K n)
  unfold BoundedGeneratorSectors
  rw [Nat.card_sigma]
  exact Finset.sum_congr rfl fun I _ => card_generatorOrbits_eq_indicator Γ I.val.val

theorem card_boundedGeneratorSectors_le (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] (n : ℕ) :
    Nat.card (BoundedGeneratorSectors K Γ n) ≤
      Γ.index * Nat.card (BoundedNonzeroIdeals K n) := by
  letI := Fintype.ofFinite (BoundedNonzeroIdeals K n)
  unfold BoundedGeneratorSectors
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _ : BoundedNonzeroIdeals K n, Γ.index :=
      Finset.sum_le_sum fun I _ => card_generatorOrbits_le_index Γ I.val.val
    _ = _ := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

theorem card_boundedNonzeroIdeals_mono :
    Monotone (fun n => Nat.card (BoundedNonzeroIdeals K n)) := by
  intro m n hmn
  exact Nat.card_le_card_of_injective
    (fun I : BoundedNonzeroIdeals K m =>
      (⟨I.val, I.property.trans hmn⟩ : BoundedNonzeroIdeals K n))
    (by
      intro I J h
      exact Subtype.ext (congrArg (fun T : BoundedNonzeroIdeals K n => T.val) h))

theorem card_boundedNonzeroIdeals_limit :
    Tendsto (fun n : ℕ => (Nat.card (BoundedNonzeroIdeals K n) : ℝ) / n)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  simpa [BoundedNonzeroIdeals, Function.comp_def, NumberField.dedekindZeta_residue] using
    (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop

/-- A single field-dependent constant controls every integral norm cutoff. -/
theorem exists_card_boundedNonzeroIdeals_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Nat.card (BoundedNonzeroIdeals K n) : ℝ) ≤ C * (1 + n) := by
  have hO : (fun n : ℕ => (Nat.card (BoundedNonzeroIdeals K n) : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (by simpa using card_boundedNonzeroIdeals_limit K)
  obtain ⟨c, hc, hbound⟩ := hO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound.bound
  let C := c + (Nat.card (BoundedNonzeroIdeals K N) : ℝ)
  have hCN : (Nat.card (BoundedNonzeroIdeals K N) : ℝ) ≤ C := by
    dsimp [C]
    linarith
  have hcC : c ≤ C := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h : (Nat.card (BoundedNonzeroIdeals K n) : ℝ) ≤ c * n := by
      simpa only [Real.rpow_one, Real.norm_natCast] using hN n hn
    calc
      _ ≤ c * n := h
      _ ≤ C * n := mul_le_mul_of_nonneg_right hcC (Nat.cast_nonneg n)
      _ ≤ C * (1 + n) := mul_le_mul_of_nonneg_left (by linarith) hC.le
  · have h : (Nat.card (BoundedNonzeroIdeals K n) : ℝ) ≤
        (Nat.card (BoundedNonzeroIdeals K N) : ℝ) := by
      exact_mod_cast card_boundedNonzeroIdeals_mono K (le_of_not_ge hn)
    calc
      _ ≤ C := h.trans hCN
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (1 + n) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Nat.cast_nonneg n)) hC.le

/-- The unit-sector index is retained in the uniform linear count. -/
theorem exists_card_boundedGeneratorSectors_le (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Nat.card (BoundedGeneratorSectors K Γ n) : ℝ) ≤
        (Γ.index : ℝ) * C * (1 + n) := by
  obtain ⟨C, hC, h⟩ := exists_card_boundedNonzeroIdeals_le K
  refine ⟨C, hC, fun n => ?_⟩
  have hcard : (Nat.card (BoundedGeneratorSectors K Γ n) : ℝ) ≤
      (Γ.index : ℝ) * (Nat.card (BoundedNonzeroIdeals K n) : ℝ) := by
    exact_mod_cast card_boundedGeneratorSectors_le K Γ n
  exact hcard.trans (by simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left (h n) (Nat.cast_nonneg Γ.index))

end HeckeGeneral.Arithmetic
