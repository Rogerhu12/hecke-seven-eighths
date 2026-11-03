import HeckeGeneral.Analysis.ExpansionReflectedPolynomials
import ExpansionDetector.MellinScaleBounds

/-! Uniform powers of the row scale for the actual analytic constants.
The only inputs are the actual ideal norm, actual conductor, and physical
height size comparisons; no polynomial estimate is assumed. -/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionScaleBounds

open NumberField IsDedekindDomain HeckeGeneral.Characters
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open ExpansionDeletedControl ExpansionReflectedPolynomials ExpansionDetector.PowerBudget

variable (K : Type) [Field K] [NumberField K]

def heightDegree : ℝ := (2 * Fintype.card (InfinitePlace K) : ℕ)

theorem bufferedCost_le_scale (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
    (C R ε U θ Hupper : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hU : 0 < U) (hH : 0 ≤ Hupper)
    (hI : (Ideal.absNorm I : ℝ) ≤ R * U)
    (hQ : heckeConductorScale K χ ≤ R * U)
    (hheight : 2 + Hupper ≤ R * U ^ θ) :
    bufferedCost K χ I C ε Hupper ≤
      bufferedScaleConstant C R ε (heightDegree K) *
        U ^ (2 * ε + heightDegree K * ε * θ) := by
  exact buffered_monomial_scale_bound C R ε (heightDegree K) U θ
    (Ideal.absNorm I : ℝ) (heckeConductorScale K χ) (2 + Hupper)
    hC hR hε (by unfold heightDegree; positivity) hU (Nat.cast_nonneg _)
    (conductorScale_pos K χ).le (by positivity) hI hQ hheight

theorem reflectedCost_le_scale (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
    (C R e ε U θ a Hupper : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (he : 0 ≤ e) (he' : e ≤ 1 / 12) (hε : 0 ≤ ε)
    (hU : 0 < U) (hH : 0 ≤ Hupper)
    (hI : (Ideal.absNorm I : ℝ) ≤ R * U)
    (hQ : heckeConductorScale K χ ≤ R * U)
    (hheight : 2 + Hupper ≤ R * U ^ θ) (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) :
    reflectedCost K χ I C e ε a Hupper ≤
      reflectedScaleConstant C R e ε (heightDegree K) *
        U ^ (a - 1 / 2 + 12 * e + 2 * ε + heightDegree K * θ * (1 + ε)) := by
  have h := reflected_monomial_scale_bound C R e ε (heightDegree K) U θ
    (Ideal.absNorm I : ℝ) (heckeConductorScale K χ) (2 + Hupper) a
    hC hR he he' hε (by unfold heightDegree; positivity) hU (Nat.cast_nonneg _)
    (conductorScale_pos K χ).le (by positivity) hI hQ hheight ha ha'
  simpa only [reflectedCost, heightDegree, Real.rpow_natCast] using h

theorem coarseRectangleCost_le_scale (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
    (C R ε U θ Hupper : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hU : 0 < U) (hH : 0 ≤ Hupper)
    (hI : (Ideal.absNorm I : ℝ) ≤ R * U)
    (hQ : heckeConductorScale K χ ≤ R * U)
    (hheight : 2 + Hupper ≤ R * U ^ θ) :
    coarseRectangleCost K χ I C ε Hupper ≤
      coarseScaleConstant C R ε (heightDegree K) * U ^ (3 / 4 + ε + heightDegree K * θ) := by
  have h := coarse_monomial_scale_bound C R ε (heightDegree K) U θ
    (Ideal.absNorm I : ℝ) (heckeConductorScale K χ) (2 + Hupper)
    hC hR hε (by unfold heightDegree; positivity) hU (Nat.cast_nonneg _)
    (conductorScale_pos K χ).le (by positivity) hI hQ hheight
  simpa only [coarseRectangleCost, heightDegree, Real.rpow_natCast] using h

end HeckeGeneral.Analysis.ExpansionScaleBounds
