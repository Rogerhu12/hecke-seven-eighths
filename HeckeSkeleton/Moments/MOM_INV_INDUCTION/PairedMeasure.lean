import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linearizing the two child energies with one common measure

The published fixed-triple provider first bounds a signed reconstructed
block by two Cauchy roots with the same frozen-triple measure. This file
proves the elementary linearization needed for a linear child-energy
consumer. The paired children are the original triples times `Bool`,
each with weight `w γ / (2 * D)`. Their mass is at most one when the
original mass is at most `D`, and rescaling restores the original mass
exactly once.

This is only the finite-measure ingredient. It does not identify the
provider's packet columns with canonical columns or reconstruct a whole
parent from the fixed blocks; those obligations remain explicit in
`STATEMENT_AUDIT.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped BigOperators Classical

variable {ι : Type*}

/-- The same original triple is used once for each of the two child columns. -/
def pairedChildren (triples : Finset ι) : Finset (ι × Bool) :=
  triples ×ˢ Finset.univ

/-- The factor two pays for the two sides of the Cauchy product. -/
def pairedWeight (weight : ι → ℝ) (D : ℝ) (q : ι × Bool) : ℝ :=
  weight q.1 / (2 * D)

def pairedValue (left right : ι → ℝ) (q : ι × Bool) : ℝ :=
  if q.2 then left q.1 else right q.1

/-- Arithmetic-geometric mean applied after the two positive sums. -/
theorem weighted_two_roots_le_half_sum (triples : Finset ι)
    (weight left right : ι → ℝ)
    (hw : ∀ γ ∈ triples, 0 ≤ weight γ)
    (hleft : ∀ γ ∈ triples, 0 ≤ left γ)
    (hright : ∀ γ ∈ triples, 0 ≤ right γ) :
    Real.sqrt (∑ γ ∈ triples, weight γ * left γ) *
        Real.sqrt (∑ γ ∈ triples, weight γ * right γ) ≤
      (∑ γ ∈ triples, weight γ * (left γ + right γ)) / 2 := by
  have hL : 0 ≤ ∑ γ ∈ triples, weight γ * left γ :=
    Finset.sum_nonneg (fun γ hγ => mul_nonneg (hw γ hγ) (hleft γ hγ))
  have hR : 0 ≤ ∑ γ ∈ triples, weight γ * right γ :=
    Finset.sum_nonneg (fun γ hγ => mul_nonneg (hw γ hγ) (hright γ hγ))
  rw [show (∑ γ ∈ triples, weight γ * (left γ + right γ)) =
      (∑ γ ∈ triples, weight γ * left γ) +
        (∑ γ ∈ triples, weight γ * right γ) by
    simp only [mul_add, Finset.sum_add_distrib]]
  nlinarith [Real.sq_sqrt hL, Real.sq_sqrt hR,
    sq_nonneg (Real.sqrt (∑ γ ∈ triples, weight γ * left γ) -
      Real.sqrt (∑ γ ∈ triples, weight γ * right γ))]

theorem pairedWeight_nonneg (triples : Finset ι) (weight : ι → ℝ)
    {D : ℝ} (hD : 0 < D) (hw : ∀ γ ∈ triples, 0 ≤ weight γ)
    (q : ι × Bool) (hq : q ∈ pairedChildren triples) :
    0 ≤ pairedWeight weight D q := by
  exact div_nonneg (hw q.1 (Finset.mem_product.mp hq).1)
    (mul_nonneg (by norm_num) hD.le)

/-- Expanding the paired index set does not alter either original measure. -/
theorem paired_weighted_sum_eq (triples : Finset ι)
    (weight left right : ι → ℝ) (D : ℝ) :
    (∑ q ∈ pairedChildren triples, pairedWeight weight D q * pairedValue left right q) =
      (∑ γ ∈ triples, weight γ * (left γ + right γ)) / (2 * D) := by
  unfold pairedChildren pairedWeight pairedValue
  rw [Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro γ _
  simp only [Fintype.sum_bool]
  dsimp
  ring

/-- The two side weights sum to one copy of the original triple mass. -/
theorem pairedWeight_mass_eq (triples : Finset ι) (weight : ι → ℝ)
    {D : ℝ} (hD : 0 < D) :
    (∑ q ∈ pairedChildren triples, pairedWeight weight D q) =
      (∑ γ ∈ triples, weight γ) / D := by
  have h := paired_weighted_sum_eq triples weight (fun _ => 1) (fun _ => 1) D
  simp only [pairedValue, ite_self, mul_one] at h
  rw [h, ← Finset.sum_mul]
  field_simp [hD.ne'] <;> ring

theorem pairedWeight_mass_le (triples : Finset ι) (weight : ι → ℝ)
    {D : ℝ} (hD : 0 < D) (hmass : ∑ γ ∈ triples, weight γ ≤ D) :
    ∑ q ∈ pairedChildren triples, pairedWeight weight D q ≤ 1 := by
  rw [pairedWeight_mass_eq triples weight hD]
  exact (div_le_iff₀ hD).mpr (by simpa using hmass)

/-- Restoring the extracted mass leaves one half of the sum of the two
original positive energies, with no extra triple count. -/
theorem paired_sum_rescale (triples : Finset ι)
    (weight left right : ι → ℝ) {D : ℝ} (hD : 0 < D) :
    D * (∑ q ∈ pairedChildren triples,
      pairedWeight weight D q * pairedValue left right q) =
        (∑ γ ∈ triples, weight γ * (left γ + right γ)) / 2 := by
  rw [paired_weighted_sum_eq]
  field_simp [hD.ne'] <;> ring

/-- The two Cauchy roots are bounded by a linear sum over genuine paired
children. Its weight nonnegativity and mass bound are proved separately. -/
theorem weighted_two_roots_le_paired_sum (triples : Finset ι)
    (weight left right : ι → ℝ) {D : ℝ} (hD : 0 < D)
    (hw : ∀ γ ∈ triples, 0 ≤ weight γ)
    (hleft : ∀ γ ∈ triples, 0 ≤ left γ)
    (hright : ∀ γ ∈ triples, 0 ≤ right γ) :
    Real.sqrt (∑ γ ∈ triples, weight γ * left γ) *
        Real.sqrt (∑ γ ∈ triples, weight γ * right γ) ≤
      D * (∑ q ∈ pairedChildren triples,
        pairedWeight weight D q * pairedValue left right q) := by
  rw [paired_sum_rescale triples weight left right hD]
  exact weighted_two_roots_le_half_sum triples weight left right hw hleft hright

/-- Inserting one common child bound restores exactly one original
triple mass, independent of the chosen positive normalization `D`. -/
theorem paired_constant_rescale (triples : Finset ι) (weight : ι → ℝ)
    {D : ℝ} (hD : 0 < D) (H : ℝ) :
    D * (∑ q ∈ pairedChildren triples, pairedWeight weight D q * H) =
      H * ∑ γ ∈ triples, weight γ := by
  calc
    _ = (∑ γ ∈ triples, weight γ * (H + H)) / 2 := by
      simpa only [pairedValue, ite_self] using
        paired_sum_rescale triples weight (fun _ => H) (fun _ => H) hD
    _ = _ := by
      rw [← Finset.sum_mul]
      ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

