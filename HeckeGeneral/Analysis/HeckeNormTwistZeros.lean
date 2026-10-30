import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Analysis.MellinZeroDetector

/-! Removing a global unitary norm twist preserves the actual meromorphic
zero real parts. Continuation uniqueness is used at the germ level, so no
pointwise equality at arbitrarily totalized poles is required. -/

noncomputable section
namespace HeckeGeneral.Analysis

open HeckeGeneral.Characters Set
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

theorem heckeContinuation_normTwist_eventuallyEq
    (χ : HeckeCharacter K) (t : ℝ) (s : ℂ) :
    (fun z => heckeContinuation K χ (z - (t : ℂ) * Complex.I)) =ᶠ[𝓝[≠] s]
      heckeContinuation K (χ * heckeNormTwist K t) := by
  apply heckeContinuation_eventuallyEq_of_meromorphic K (χ * heckeNormTwist K t)
  · intro z _
    exact (meromorphicOn_heckeContinuation K χ _ (mem_univ _)).comp_analyticAt
      (analyticAt_id.sub analyticAt_const)
  · intro z hz
    rw [heckeContinuation_eq_series K χ (by simpa using hz)]
    exact (heckeLSeries_normTwist K χ t z).symm

theorem meromorphicOrderAt_heckeContinuation_mul_normTwist
    (χ : HeckeCharacter K) (t : ℝ) (s : ℂ) :
    meromorphicOrderAt (heckeContinuation K (χ * heckeNormTwist K t)) s =
      meromorphicOrderAt (heckeContinuation K χ) (s - (t : ℂ) * Complex.I) := by
  rw [← meromorphicOrderAt_congr (heckeContinuation_normTwist_eventuallyEq K χ t s)]
  exact meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt

theorem zeroRealParts_heckeContinuation_normTwist (χ : HeckeCharacter K) (t : ℝ) :
    zeroRealParts (heckeContinuation K (χ * heckeNormTwist K t)) =
      zeroRealParts (heckeContinuation K χ) := by
  ext r
  constructor
  · rintro ⟨s, hsr, hs⟩
    refine ⟨s - (t : ℂ) * Complex.I, ?_, ?_⟩
    · simpa using hsr
    · rwa [meromorphicOrderAt_heckeContinuation_mul_normTwist] at hs
  · rintro ⟨s, hsr, hs⟩
    refine ⟨s + (t : ℂ) * Complex.I, ?_, ?_⟩
    · simpa using hsr
    · simpa only [meromorphicOrderAt_heckeContinuation_mul_normTwist, add_sub_cancel_right]
        using hs

theorem heckeContinuation_normTwist_zeroFreeOn_iff
    (χ : HeckeCharacter K) (t b : ℝ) :
    MeromorphicZeroFreeOn (heckeContinuation K (χ * heckeNormTwist K t))
        (rightHalfPlane b) ↔
      MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane b) := by
  constructor
  · intro h
    refine ⟨fun s _ => meromorphicOn_heckeContinuation K χ s (mem_univ _), ?_⟩
    intro s hs
    have he := h.2 (s + (t : ℂ) * Complex.I) (by simpa [rightHalfPlane] using hs)
    simpa only [meromorphicOrderAt_heckeContinuation_mul_normTwist, add_sub_cancel_right] using he
  · intro h
    refine ⟨fun s _ => meromorphicOn_heckeContinuation K _ s (mem_univ _), ?_⟩
    intro s hs
    rw [meromorphicOrderAt_heckeContinuation_mul_normTwist]
    exact h.2 _ (by simpa [rightHalfPlane] using hs)

end HeckeGeneral.Analysis
