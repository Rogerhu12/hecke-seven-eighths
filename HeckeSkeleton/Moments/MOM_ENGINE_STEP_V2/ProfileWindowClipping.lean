import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalClippedProfileBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Internal broad support window for actual clipping

The two actual clipping factors are computed from the original real
parameters. Every label is retained. Their maximum pays the seminorm
cost, without an activity or nonzero-source assumption. The clipped
profiles lie in `[0,B]`; the original positive raw window is not replaced.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileWindowProof

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open EngineStep EngineStep.CanonicalLogProfiles

/-- The maximum of the two literal positive plain-clipping factors. -/
def actualClippingBound (Z : ℝ) (p : RealParameters) : ℝ :=
  max (plainClippingFactor Z p.n₁) (plainClippingFactor Z p.n₂)

theorem actualClippingBound_one_le (Z : ℝ) (p : RealParameters) (hZ : 1 ≤ Z) :
    1 ≤ actualClippingBound Z p :=
  (plainClippingFactor_one_le Z p.n₁ hZ).trans (le_max_left _ _)

/-- The exact common seminorm cost of the two original clipping factors. -/
def actualClippingCoefficient (Z : ℝ) (p : RealParameters)
    (orders : Finset (ℕ × ℕ)) : ℝ :=
  clippingCoefficient (actualClippingBound Z p) orders

theorem actualClippingCoefficient_one_le (Z : ℝ) (p : RealParameters)
    (orders : Finset (ℕ × ℕ)) (hZ : 1 ≤ Z) :
    1 ≤ actualClippingCoefficient Z p orders :=
  clippingCoefficient_one_le _ (actualClippingBound_one_le Z p hZ) orders

/-- Once activity supplies the two original upper bounds, the computed
cost is bounded by the original fixed-window clipping cost. -/
theorem actualClippingCoefficient_le (Z : ℝ) (p : RealParameters)
    (orders : Finset (ℕ × ℕ)) (hZ : 1 ≤ Z) (B : ℝ)
    (hleft : plainClippingFactor Z p.n₁ ≤ B)
    (hright : plainClippingFactor Z p.n₂ ≤ B) :
    actualClippingCoefficient Z p orders ≤ clippingCoefficient B orders := by
  have hbound : actualClippingBound Z p ≤ B := max_le hleft hright
  have hnonneg : 0 ≤ actualClippingBound Z p :=
    zero_le_one.trans (actualClippingBound_one_le Z p hZ)
  unfold actualClippingCoefficient clippingCoefficient
  exact mul_le_mul (Real.sqrt_le_sqrt hbound)
    (pow_le_pow_left₀ hnonneg hbound (orders.sup Prod.snd))
    (pow_nonneg hnonneg _) (Real.sqrt_nonneg _)

private theorem originalAnnulus_subset_broad (a B : ℝ) (ha : 0 < a) :
    Set.Icc a B ⊆ Set.Icc 0 B := by
  intro x hx
  exact ⟨ha.le.trans hx.1, hx.2⟩

/-- Every positive dilation at least one preserves the broad upper
window, even when its factor exceeds the original upper endpoint. -/
theorem dilationSchwartz_support_broad (a B : ℝ) (ha : 0 < a)
    (c : ℝ) (hc : 1 ≤ c) (φ : 𝓢(ℝ, ℂ))
    (hsupport : Function.support φ ⊆ Set.Icc a B) :
    Function.support (dilationSchwartz c hc φ) ⊆ Set.Icc 0 B := by
  intro y hy
  change (Real.sqrt c : ℂ) * φ (c * y) ≠ 0 at hy
  have hφ : φ (c * y) ≠ 0 := right_ne_zero_of_mul hy
  have hcy := hsupport hφ
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hy0 : 0 < y := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_not_gt h)
    linarith [hcy.1]
  refine ⟨hy0.le, ?_⟩
  have hyc : y ≤ c * y := by nlinarith
  exact hyc.trans hcy.2

section Windows

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}

/-- Construct the actual clipped window for every raw label. The
original inverse and prime representatives are retained, while the two
plain representatives use precisely the prescribed square-root dilation.
No nonzero-energy, activity, or bounded-clipping-factor hypothesis enters. -/
def clipRawWindow_broad (d : MomentData K ω ψ) (p : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (orders : Finset (ℕ × ℕ)) {A : ℝ} (hA : 0 ≤ A)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B) orders d A) :
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 B) orders
      (clipPlainData d p Z (zero_lt_one.trans_le hZ))
      (actualClippingCoefficient Z p orders * A) := by
  let c₁ := plainClippingFactor Z p.n₁
  let c₂ := plainClippingFactor Z p.n₂
  let C := actualClippingBound Z p
  have hc₁ : 1 ≤ c₁ := plainClippingFactor_one_le Z p.n₁ hZ
  have hc₂ : 1 ≤ c₂ := plainClippingFactor_one_le Z p.n₂ hZ
  have hC : 1 ≤ C := actualClippingBound_one_le Z p hZ
  have hc₁C : c₁ ≤ C := le_max_left _ _
  have hc₂C : c₂ ≤ C := le_max_right _ _
  have hRone : 1 ≤ actualClippingCoefficient Z p orders :=
    actualClippingCoefficient_one_le Z p orders hZ
  have hR : 0 ≤ actualClippingCoefficient Z p orders := zero_le_one.trans hRone
  have hAR : A ≤ actualClippingCoefficient Z p orders * A := by
    simpa only [mul_comm] using le_mul_of_one_le_right hA hRone
  refine
    { inverseRep := w.inverseRep
      leftRep := fun u t => dilationSchwartz c₁ hc₁ (w.leftRep u t)
      rightRep := fun u t => dilationSchwartz c₂ hc₂ (w.rightRep u t)
      primeRep := w.primeRep
      inverse_eq := w.inverse_eq
      left_eq := ?_
      right_eq := ?_
      prime_eq := w.prime_eq
      inverse_support := fun u hu t ht =>
        (w.inverse_support u hu t ht).trans (originalAnnulus_subset_broad a B ha)
      left_support := fun u hu t ht => dilationSchwartz_support_broad a B ha c₁ hc₁
        (w.leftRep u t) (w.left_support u hu t ht)
      right_support := fun u hu t ht => dilationSchwartz_support_broad a B ha c₂ hc₂
        (w.rightRep u t) (w.right_support u hu t ht)
      prime_support := fun i t ht =>
        (w.prime_support i t ht).trans (originalAnnulus_subset_broad a B ha)
      inverse_bound := fun u hu t ht => (w.inverse_bound u hu t ht).trans hAR
      left_bound := fun u hu t ht =>
        (dilationSchwartz_finset_bound C hC orders c₁ hc₁ hc₁C (w.leftRep u t)).trans
          (mul_le_mul_of_nonneg_left (w.left_bound u hu t ht) hR)
      right_bound := fun u hu t ht =>
        (dilationSchwartz_finset_bound C hC orders c₂ hc₂ hc₂C (w.rightRep u t)).trans
          (mul_le_mul_of_nonneg_left (w.right_bound u hu t ht) hR)
      prime_bound := fun i t ht => (w.prime_bound i t ht).trans hAR }
  · intro u t y
    change (Real.sqrt c₁ : ℂ) * d.plainTest₁.profile u t (c₁ * y) = _
    rw [dilationSchwartz_apply, w.left_eq]
  · intro u t y
    change (Real.sqrt c₂ : ℂ) * d.plainTest₂.profile u t (c₂ * y) = _
    rw [dilationSchwartz_apply, w.right_eq]

end Windows
end HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileWindowProof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileWindowProof.actualClippingCoefficient_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileWindowProof.clipRawWindow_broad
