import HeckeSkeleton.HighBinSupport.HighNormFormScalar
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Order.Compact
/-!
Finite slot bounds with the complete main/error decomposition retained.
The theorems allow zero main slots.  They do not divide by a main slot,
a Gauss polynomial, or an unmarked Euler factor.
-/

noncomputable section
namespace HighBinVerified.NormForm
open scoped BigOperators

/-- Literal expansion into all error subsets, including zero factors. -/
theorem full_slot_expansion {ι : Type*} [DecidableEq ι] (s : Finset ι) (main error : ι → ℂ) :
    (∏ i ∈ s, (main i + error i)) =
      ∑ J ∈ s.powerset, (∏ i ∈ J, error i) * ∏ i ∈ s \ J, main i := by
  simpa only [add_comm] using Finset.prod_add error main s

/-- One complete slot product with arbitrary slot lengths.  The amplitude
contribution is weighted in base Z. -/
theorem weighted_slot_product_bound {ι : Type*} (s : Finset ι)
    (Z mesh : ℝ) (length amplitude constant : ι → ℝ) (f : ι → ℂ)
    (hZ : 0 < Z)
    (hf : ∀ i ∈ s, ‖f i‖ ≤
      constant i * (Z ^ length i) ^ (-4 / 25 + amplitude i + mesh)) :
    ‖∏ i ∈ s, f i‖ ≤ (∏ i ∈ s, constant i) *
      Z ^ ((-4 / 25 + mesh) * (∑ i ∈ s, length i) +
        ∑ i ∈ s, length i * amplitude i) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i ∈ s, constant i * (Z ^ length i) ^ (-4 / 25 + amplitude i + mesh) :=
      Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) hf
    _ = (∏ i ∈ s, constant i) *
        ∏ i ∈ s, Z ^ (length i * (-4 / 25 + amplitude i + mesh)) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.rpow_mul hZ.le _ _).symm
    _ = (∏ i ∈ s, constant i) *
        Z ^ (∑ i ∈ s, length i * (-4 / 25 + amplitude i + mesh)) := by
      rw [Real.rpow_sum_of_pos hZ]
    _ = _ := by
      congr 2
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Uniform slot lengths give exactly q/6, with q the mean amplitude.
This is a power of Z, rather than of U=Z^d. -/
theorem uniform_slot_product_bound (J : ℕ) (hJ : 0 < J)
    (Z mesh C : ℝ) (g : Fin J → ℝ) (f : Fin J → ℂ)
    (hZ : 0 < Z)
    (hf : ∀ i, ‖f i‖ ≤ C * (Z ^ ((1 / 6 : ℝ) / J)) ^
      (-4 / 25 + g i + mesh)) :
    ‖∏ i, f i‖ ≤ C ^ J *
      Z ^ (-2 / 75 + ((∑ i, g i) / J) / 6 + mesh / 6) := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hJ
  have hlength : (∑ _i : Fin J, (1 / 6 : ℝ) / J) = 1 / 6 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hweight : (∑ i : Fin J, ((1 / 6 : ℝ) / J) * g i) =
      ((∑ i, g i) / J) / 6 := by
    rw [← Finset.mul_sum]
    ring
  have hh := weighted_slot_product_bound (Finset.univ : Finset (Fin J))
    Z mesh (fun _ => (1 / 6 : ℝ) / J) g (fun _ => C) f hZ (fun i _ => hf i)
  simpa only [hlength, hweight, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, show (-4 / 25 + mesh) * (1 / 6) + ((∑ i, g i) / J) / 6 =
      -2 / 75 + ((∑ i, g i) / J) / 6 + mesh / 6 by ring] using hh

/-- Every selected error slot is retained. -/
theorem selected_error_slot_bound {ι : Type*} [DecidableEq ι]
    (selected : Finset ι) (main error : ι → ℂ) (bound : ι → ℝ)
    (hmain : ∀ i, i ∉ selected → ‖main i‖ ≤ bound i)
    (herror : ∀ i ∈ selected, ‖error i‖ ≤ bound i) :
    ∀ i, ‖if i ∈ selected then error i else main i‖ ≤ bound i := by
  intro i
  split_ifs with hi
  · exact herror i hi
  · exact hmain i hi

/-- A continuous physical slot has an actual maximizer on the retained
height interval.  The maximizing height may depend on both row and slot. -/
theorem exists_slot_maximizer (f : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H)
    (hf : ContinuousOn f (Set.Icc (-H) H)) :
    ∃ t ∈ Set.Icc (-H) H, ∀ x ∈ Set.Icc (-H) H, ‖f x‖ ≤ ‖f t‖ := by
  have hne : (Set.Icc (-H) H).Nonempty := ⟨0, by constructor <;> linarith⟩
  exact isCompact_Icc.exists_isMaxOn hne hf.norm

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.full_slot_expansion
#print axioms HighBinVerified.NormForm.weighted_slot_product_bound
#print axioms HighBinVerified.NormForm.uniform_slot_product_bound
#print axioms HighBinVerified.NormForm.exists_slot_maximizer
