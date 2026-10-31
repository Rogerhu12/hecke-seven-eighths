import HeckeSkeleton.Moments.MOM_INV_INDUCTION.Uniform

/-!
# Height order before an outer tolerance parameter

The descent budget and input height order are common to the entire
family.  The scalar constants may depend on an outer parameter, such as
the tolerance in `UniformMomentBound`.  A dependent source index permits
the admissible scales, including an eventual threshold, to vary with
that parameter.  All source and scale conditions remain explicit inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- The height order is chosen before the outer parameter, while the
positive scalar may depend on it.  The witnesses are
`A * (b.depth + 1)` and
`((Fintype.card σ : ℝ) + 1) * (9 * C t * L t) ^ (b.depth + 1)`.
The index `I t` can contain exactly the scales above a threshold depending
on `t`, together with all permitted labels and rowwise parameters. -/
theorem uniform_outer_canonical_inverse_sector_models
    {T σ α : Type*} [Fintype σ] {I : T → Type*}
    {ω ψ : HeckeCharacter K} (source : ∀ t, I t → σ → MomentData K ω ψ)
    (a : ∀ t, I t → RealParameters) (Z H : ∀ t, I t → ℝ)
    (node : ∀ t, I t → σ → α → CanonicalDatum K) (C L : T → ℝ)
    {Mmax c eps A : ℝ} (b : DescentBudget Mmax c eps)
    (p : ∀ t i s, CanonicalInputs (node t i s) b (Z t i) (C t) (L t) (H t i) A)
    (q : ∀ t i s, InitialInputs (node t i s) (p t i s)
      (inverseEnergy (source t i s) (a t i) (Z t i) 0)
      (a t i).m (a t i).r (a t i).z)
    (hMmax : 0 ≤ Mmax) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : ∀ t, 1 ≤ C t) (hL : ∀ t, 1 ≤ L t)
    (hZ : ∀ t i, 1 ≤ Z t i) (hH : ∀ t i, 1 ≤ H t i)
    (h₁ : ∀ t i, (a t i).r + 2 * (a t i).z ≤ (a t i).m - 4 * c / 3)
    (h₂ : ∀ t i, 2 * (a t i).r + 8 * (a t i).z ≤ 3 * (a t i).m - 4 * c / 3) :
    ∃ Astar : ℝ, 0 ≤ Astar ∧ ∀ t, ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ i : I t, (∑ s, inverseEnergy (source t i s) (a t i) (Z t i) 0) ≤
        Cstar * (Z t i) ^ ((a t i).m + eps) * (H t i) ^ Astar := by
  refine ⟨A * ((b.depth + 1 : ℕ) : ℝ), mul_nonneg hA (Nat.cast_nonneg _), ?_⟩
  intro t
  have hCp : 0 < C t := zero_lt_one.trans_le (hC t)
  have hLp : 0 < L t := zero_lt_one.trans_le (hL t)
  have hconst : 0 < (9 * C t * L t) ^ (b.depth + 1) := by positivity
  refine ⟨((Fintype.card σ : ℝ) + 1) * (9 * C t * L t) ^ (b.depth + 1),
    by positivity, ?_⟩
  intro i
  have hW : 0 ≤ (Z t i) ^ ((a t i).m + eps) *
      (H t i) ^ (A * ((b.depth + 1 : ℕ) : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hZ t i)) _)
      (Real.rpow_nonneg (zero_le_one.trans (hH t i)) _)
  have hscalar : 3 * (3 * C t * L t) = 9 * C t * L t := by ring
  simpa only [Finset.card_univ, mul_assoc] using
    finite_sector_energy_bound Finset.univ
      (fun s => inverseEnergy (source t i s) (a t i) (Z t i) 0) hconst.le hW
      (fun s _ => by
        simpa only [hscalar, mul_assoc] using
          canonical_inverse_models (source t i s) (a t i) b (p t i s) (q t i s)
            hMmax hc (hZ t i) (hC t) (hL t) (hH t i) hA (h₁ t i) (h₂ t i))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
