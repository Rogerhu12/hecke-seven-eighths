module

public import HeckeGeneral.Analysis.HeckeNormPole
public import HeckeGeneral.Analysis.MellinZeroDetector

@[expose] public section

/-!
# A pointwise continuation for the Mathlib-only Hecke challenge

The existing simple-pole theorem for norm characters supplies a nonzero
pole-cleared numerator. Choosing its quotient gives the genuine exceptional
point required by the challenge. Equality of meromorphic germs transfers
zero-freeness from the chosen library continuation to this quotient.
For all other characters, the library continuation is entire.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Characters Filter
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

/-- Convert genuine meromorphic zero-freeness into a pointwise continuation
with at most one genuine simple pole. The series itself is unchanged. -/
theorem exists_challengeContinuation (χ : HeckeCharacter K)
    (hfree : MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (7 / 8))) :
    ∃ f : ℂ → ℂ, ∃ P : Set ℂ, P.Subsingleton ∧
      DifferentiableOn ℂ f Pᶜ ∧
      (∀ p ∈ P, p.re = 1 ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ g p ≠ 0 ∧
        ∀ᶠ s in 𝓝[≠] p, f s = g s / (s - p)) ∧
      (∀ s : ℂ, 1 < s.re → f s = heckeLSeries K χ s) ∧
      ∀ s : ℂ, 7 / 8 < s.re → s ∉ P → f s ≠ 0 := by
  classical
  by_cases hnorm : ∃ t : ℝ, χ = heckeNormTwist K t
  · obtain ⟨t, rfl⟩ := hnorm
    obtain ⟨Q, hQ, hQ0, hQeq⟩ := exists_nonzero_poleCleared_normTwist K t
    let p : ℂ := heckeNormPole t
    let L : ℂ → ℂ := fun s => Q s / (s - p)
    have hL : MeromorphicOn L Set.univ := by
      intro s _hs
      exact (hQ.analyticAt s).meromorphicAt.div
        (analyticAt_id.sub analyticAt_const).meromorphicAt
    have hLeq : ∀ s : ℂ, 1 < s.re →
        L s = heckeLSeries K (heckeNormTwist K t) s := by
      intro s hs
      dsimp only [L, p]
      rw [hQeq s hs]
      exact mul_div_cancel_left₀ _ (sub_heckeNormPole_ne_zero hs t)
    have hLfree : MeromorphicZeroFreeOn L (rightHalfPlane (7 / 8)) := by
      refine ⟨fun s _hs => hL s (Set.mem_univ s), ?_⟩
      intro s hs
      rw [meromorphicOrderAt_congr
        (heckeContinuation_eventuallyEq_of_meromorphic K (heckeNormTwist K t)
          L hL hLeq s)]
      exact hfree.2 s hs
    have hLanalytic : ∀ s : ℂ, s ≠ p → AnalyticAt ℂ L s := by
      intro s hs
      exact (hQ.analyticAt s).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hs)
    refine ⟨L, {p}, Set.subsingleton_singleton, ?_, ?_, hLeq, ?_⟩
    · intro s hs
      exact (hLanalytic s (by simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using hs)).differentiableAt.differentiableWithinAt
    · intro q hq
      have hqp : q = p := Set.mem_singleton_iff.mp hq
      subst q
      refine ⟨?_, Q, hQ.analyticAt p, hQ0, Filter.Eventually.of_forall (fun _ => rfl)⟩
      simp [p, heckeNormPole]
    · intro s hs hsp
      exact hLfree.ne_zero hs
        (hLanalytic s (by simpa only [Set.mem_singleton_iff] using hsp))
  · have hn : ∀ t : ℝ, χ ≠ heckeNormTwist K t := fun t ht => hnorm ⟨t, ht⟩
    have hd := differentiable_heckeContinuation_of_nonNorm K χ hn
    refine ⟨heckeContinuation K χ, ∅, Set.subsingleton_empty, hd.differentiableOn,
      ?_, ?_, ?_⟩
    · intro p hp
      exact False.elim (Set.notMem_empty p hp)
    · intro s hs
      exact heckeContinuation_eq_series K χ hs
    · intro s hs _hsp
      exact hfree.ne_zero hs (hd.analyticAt s)

end HeckeGeneral.Analysis
