import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ActualMoments

/-!
# Uniformity across an entire explicit source family

The depth, margin, loss, and profile constants precede the source index.
Thus the resulting constant and height order are common to every scale,
label, sector, surviving subset and permitted rowwise parameter choice
included in that index.  This theorem does not infer a common input from
unrelated per-index constants or from one-variable slice seminorm bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

/-- One finite constant and one height order for the whole marked family.
The index type may contain all continuous and rowwise parameters. -/
theorem uniform_canonical_inverse_models {ι α : Type*}
    {ω ψ : HeckeCharacter K} (source : ι → MomentData K ω ψ)
    (a : ι → RealParameters) (Z H : ι → ℝ) (node : ι → α → CanonicalDatum K)
    {Mmax c eps C L A : ℝ} (b : DescentBudget Mmax c eps)
    (p : ∀ i, CanonicalInputs (node i) b (Z i) C L (H i) A)
    (q : ∀ i, InitialInputs (node i) (p i)
      (inverseEnergy (source i) (a i) (Z i) 0) (a i).m (a i).r (a i).z)
    (hMmax : 0 ≤ Mmax) (hc : 0 < c) (hC : 1 ≤ C) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hZ : ∀ i, 1 ≤ Z i) (hH : ∀ i, 1 ≤ H i)
    (h₁ : ∀ i, (a i).r + 2 * (a i).z ≤ (a i).m - 4 * c / 3)
    (h₂ : ∀ i, 2 * (a i).r + 8 * (a i).z ≤ 3 * (a i).m - 4 * c / 3) :
    ∃ Cstar Astar : ℝ, 0 < Cstar ∧ 0 ≤ Astar ∧
      ∀ i, inverseEnergy (source i) (a i) (Z i) 0 ≤
        Cstar * (Z i) ^ ((a i).m + eps) * (H i) ^ Astar := by
  refine ⟨(3 * (3 * C * L)) ^ (b.depth + 1),
    A * ((b.depth + 1 : ℕ) : ℝ), ?_, ?_, ?_⟩
  · have hCp : 0 < C := zero_lt_one.trans_le hC
    have hLp : 0 < L := zero_lt_one.trans_le hL
    positivity
  · exact mul_nonneg hA (Nat.cast_nonneg _)
  · intro i
    exact canonical_inverse_models (source i) (a i) b (p i) (q i)
      hMmax hc (hZ i) hC hL (hH i) hA (h₁ i) (h₂ i)

/-- The same choice order for independent scales.  An arbitrary height
vector can be encoded by `H i = 1 + ‖ξ i‖`; all admissible rowwise twists
remain inside the source index. -/
theorem uniform_canonical_unmarked_inverse {ι α : Type*}
    {ω ψ : HeckeCharacter K} (source : ι → MomentData K ω ψ)
    (U D H : ι → ℝ) (node : ι → α → CanonicalDatum K)
    {Mmax eps C L A a : ℝ} (ha : 0 < a)
    (b : DescentBudget Mmax (3 * (a / (1 + a)) / 4) eps)
    (p : ∀ i, CanonicalInputs (node i) b (U i) C L (H i) A)
    (q : ∀ i, InitialInputs (node i) (p i)
      (independentInverseEnergy (source i) (U i) (D i)) 1 (Real.logb (U i) (D i)) 0)
    (hMmax : 0 ≤ Mmax) (hC : 1 ≤ C) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hU : ∀ i, 1 ≤ U i) (hD : ∀ i, 1 ≤ D i) (hH : ∀ i, 1 ≤ H i)
    (hcap : ∀ i, D i ≤ (U i) ^ (1 / (1 + a))) :
    ∃ Cstar Astar : ℝ, 0 < Cstar ∧ 0 ≤ Astar ∧
      ∀ i, independentInverseEnergy (source i) (U i) (D i) ≤
        Cstar * (U i) ^ (1 + eps) * (H i) ^ Astar := by
  refine ⟨(3 * (3 * C * L)) ^ (b.depth + 1),
    A * ((b.depth + 1 : ℕ) : ℝ), ?_, ?_, ?_⟩
  · have hCp : 0 < C := zero_lt_one.trans_le hC
    have hLp : 0 < L := zero_lt_one.trans_le hL
    positivity
  · exact mul_nonneg hA (Nat.cast_nonneg _)
  · intro i
    exact canonical_unmarked_inverse (source i) ha b (p i) (q i) hMmax (hU i) (hD i)
      (hcap i) hC hL (hH i) hA

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
