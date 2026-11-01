import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily

/-!
# Fibres of a dependent family of actual normalized children

An original source label has its own finite passive allocation type.
Forgetting that allocation maps each active sigma label into the sigma
of the original index fibre and its original finite inner carriers.
The count is therefore a sum of those actual inner cardinalities.

These lemmas only count the existing labels. They do not change any
source, calibration, capacity, selected child or Fourier kernel.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters

namespace ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V J I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Λ : J → Type*} {Z : ℝ}

/-- The finite-carrier version does not require a finite ambient label
type and retains each original inner carrier separately. -/
theorem activeSigma_index_fibre_card_le_sum_of_finsets
    (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
    (outer : Finset J) (labels : ∀ j, Finset (Λ j))
    (index : J → I) (i : I) :
    (Finset.univ.filter (fun b : (sigmaCombine families).active (outer.sigma labels) =>
      index b.val.1 = i)).card ≤
      ∑ j ∈ outer.filter (fun j => index j = i), (labels j).card := by
  calc
    _ ≤ ((outer.filter (fun j => index j = i)).sigma labels).card := by
      apply Finset.card_le_card_of_injOn
        (fun b : (sigmaCombine families).active (outer.sigma labels) => b.val)
      · intro b hb
        have hmem := (Finset.mem_filter.mp b.property).1
        have hsigma := Finset.mem_sigma.mp hmem
        exact Finset.mem_sigma.mpr
          ⟨Finset.mem_filter.mpr ⟨hsigma.1, (Finset.mem_filter.mp hb).2⟩, hsigma.2⟩
      · intro a ha b hb hab
        exact Subtype.ext hab
    _ = _ := Finset.card_sigma _ _

variable [Fintype J] [∀ j, Fintype (Λ j)]

/-- Each active child contributes only its original outer label and
one of that label's own original passive allocations. -/
theorem activeSigma_index_fibre_card_le_sum
    (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
    (index : J → I) (i : I) :
    (Finset.univ.filter (fun b : (sigmaCombine families).active Finset.univ =>
      index b.val.1 = i)).card ≤
      ∑ j ∈ Finset.univ.filter (fun j => index j = i), Fintype.card (Λ j) := by
  simpa only [Finset.univ_sigma_univ, Finset.card_univ] using
    activeSigma_index_fibre_card_le_sum_of_finsets families Finset.univ
      (fun _ => Finset.univ) index i

/-- A proved inner cardinality bound multiplies the original source
fibre bound. The inner estimate is required only on that same fibre. -/
theorem activeSigma_index_fibre_le
    (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
    (index : J → I) (i : I) (innerBound fibreBound : ℝ)
    (hinner0 : 0 ≤ innerBound)
    (hinner : ∀ j, index j = i → (Fintype.card (Λ j) : ℝ) ≤ innerBound)
    (hsource : ((Finset.univ.filter (fun j => index j = i)).card : ℝ) ≤ fibreBound) :
    ((Finset.univ.filter (fun b : (sigmaCombine families).active Finset.univ =>
      index b.val.1 = i)).card : ℝ) ≤ innerBound * fibreBound := by
  have hcount := activeSigma_index_fibre_card_le_sum families index i
  have hreal :
      ((Finset.univ.filter (fun b : (sigmaCombine families).active Finset.univ =>
        index b.val.1 = i)).card : ℝ) ≤
        ∑ j ∈ Finset.univ.filter (fun j => index j = i), (Fintype.card (Λ j) : ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => index j = i),
        (Fintype.card (Λ j) : ℝ) := hreal
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => index j = i), innerBound := by
      apply Finset.sum_le_sum
      intro j hj
      exact hinner j (Finset.mem_filter.mp hj).2
    _ = ((Finset.univ.filter (fun j => index j = i)).card : ℝ) * innerBound := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ fibreBound * innerBound := mul_le_mul_of_nonneg_right hsource hinner0
    _ = innerBound * fibreBound := mul_comm _ _

/-- Independent original source and passive-label subpower counts
combine without choosing new labels or changing the active family. -/
theorem activeSigma_index_fibre_subpower
    (innerConstant sourceConstant scale innerExponent sourceExponent : ℝ)
    (hscale : 0 < scale) (hinnerConstant : 0 ≤ innerConstant)
    (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
    (index : J → I)
    (hinner : ∀ j, (Fintype.card (Λ j) : ℝ) ≤ innerConstant * scale ^ innerExponent)
    (hsource : ∀ i, ((Finset.univ.filter (fun j => index j = i)).card : ℝ) ≤
      sourceConstant * scale ^ sourceExponent) :
    ∀ i, ((Finset.univ.filter (fun b : (sigmaCombine families).active Finset.univ =>
      index b.val.1 = i)).card : ℝ) ≤
        (innerConstant * sourceConstant) * scale ^ (innerExponent + sourceExponent) := by
  intro i
  have hinner0 : 0 ≤ innerConstant * scale ^ innerExponent :=
    mul_nonneg hinnerConstant (Real.rpow_nonneg hscale.le _)
  exact (activeSigma_index_fibre_le families index i
    (innerConstant * scale ^ innerExponent) (sourceConstant * scale ^ sourceExponent)
    hinner0 (fun j _ => hinner j) (hsource i)).trans_eq (by
      rw [Real.rpow_add hscale]
      ring)

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeSigma_index_fibre_card_le_sum_of_finsets
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeSigma_index_fibre_card_le_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeSigma_index_fibre_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeSigma_index_fibre_subpower
