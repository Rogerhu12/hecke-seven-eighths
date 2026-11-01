import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalHybridMass

/-!
# Fibres of the actual active rectangle family

The original leaf index is read through `activeCombineEquiv`.  The
source fibre is unchanged, while the retained rectangle is an element
of the original finite rectangle type.  The injection below counts
only active rectangles; no discarded branch is reintroduced.

For the actual two-by-two centered expansion the extra factor is four.
In particular an original uniform fibre constant is multiplied by four,
without choosing any new family, source label or scale-dependent constant.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField HeckeGeneral.Characters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V J I Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype J]
variable {Z : ℝ}

namespace ActualNormalizedPairFamily

/-- Forgetting the actual rectangle has at most `card Λ` elements in
each fibre of the original leaf index.  The original leaf may itself
be a dependent covered-source label. -/
theorem activeCombine_index_fibre_card_le [Fintype Λ]
    (families : J → ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (index : J → I) (i : I) :
    (Finset.univ.filter (fun b : (combine families).active Finset.univ =>
      index (activeCombineEquiv families b).1 = i)).card ≤
      (Finset.univ.filter (fun j => index j = i)).card * Fintype.card Λ := by
  calc
    _ ≤ ((Finset.univ.filter (fun j => index j = i)) ×ˢ
        (Finset.univ : Finset Λ)).card := by
      apply Finset.card_le_card_of_injOn
        (fun b : (combine families).active Finset.univ => (b.val.1, b.val.2))
      · intro b hb
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
        exact (Finset.mem_filter.mp hb).2
      · intro a ha b hb hab
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg Prod.fst hab
        · exact congrArg Prod.snd hab
    _ = _ := by rw [Finset.card_product, Finset.card_univ]

/-- The four original centered rectangles cost at most a factor four
over the literal covered-leaf fibre. -/
theorem activeCombine_rectangle_fibre_card_le_four
    (families : J → ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z)
    (index : J → I) (i : I) :
    (Finset.univ.filter (fun b : (combine families).active Finset.univ =>
      index (activeCombineEquiv families b).1 = i)).card ≤
      4 * (Finset.univ.filter (fun j => index j = i)).card := by
  have hfour : Fintype.card (Bool × Bool) = 4 := by decide
  calc
    _ ≤ (Finset.univ.filter (fun j => index j = i)).card *
        Fintype.card (Bool × Bool) := activeCombine_index_fibre_card_le families index i
    _ = _ := by rw [hfour, Nat.mul_comm]

/-- A proved original fibre estimate passes to the same active family.
The scalar four is independent of all source, scale and Fourier data. -/
theorem activeCombine_rectangle_fibre_le
    (families : J → ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z)
    (index : J → I) (i : I) (bound : ℝ)
    (hbound : ((Finset.univ.filter (fun j => index j = i)).card : ℝ) ≤ bound) :
    ((Finset.univ.filter (fun b : (combine families).active Finset.univ =>
      index (activeCombineEquiv families b).1 = i)).card : ℝ) ≤ 4 * bound := by
  have hn := activeCombine_rectangle_fibre_card_le_four families index i
  have hr :
      ((Finset.univ.filter (fun b : (combine families).active Finset.univ =>
        index (activeCombineEquiv families b).1 = i)).card : ℝ) ≤
        4 * ((Finset.univ.filter (fun j => index j = i)).card : ℝ) := by exact_mod_cast hn
  exact hr.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))

/-- The original constant is chosen before the moving source and is
only multiplied by four.  This does not impose a new fibre hypothesis
on the normalized family. -/
theorem activeCombine_rectangle_fibre_subpower
    (C scale ε : ℝ)
    (families : J → ActualNormalizedPairFamily A σ V (Bool × Bool) ω ψ Z)
    (index : J → I)
    (hsource : ∀ i, ((Finset.univ.filter (fun j => index j = i)).card : ℝ) ≤ C * scale ^ ε) :
    ∀ i,
      ((Finset.univ.filter (fun b : (combine families).active Finset.univ =>
        index (activeCombineEquiv families b).1 = i)).card : ℝ) ≤
          (4 * C) * scale ^ ε := by
  intro i
  exact (activeCombine_rectangle_fibre_le families index i
    (C * scale ^ ε) (hsource i)).trans_eq (by ring)

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeCombine_rectangle_fibre_card_le_four
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeCombine_rectangle_fibre_subpower
