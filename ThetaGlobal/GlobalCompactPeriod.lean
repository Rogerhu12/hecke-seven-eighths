import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith

/-!
# Differentiating a compact period

For a compact measured quotient, joint continuity of an integrand and
its pointwise derivative supplies the domination required to exchange
one real derivative with the period integral.  No unproved interchange
principle is packaged into the hypotheses: the common bound is obtained
from compactness on a closed interval times the quotient.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ThetaGlobal.GlobalCompactPeriod

theorem hasDerivAt_integral_of_joint_continuous
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (P P' : ℝ → X → ℂ)
    (hP : Continuous (Function.uncurry P))
    (hP' : Continuous (Function.uncurry P'))
    (hderiv : ∀ t q, HasDerivAt (fun s => P s q) (P' t q) t)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ q, P s q ∂μ) (∫ q, P' t q ∂μ) t := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (t - 1) (t + 1))).prod
      (isCompact_univ : IsCompact (Set.univ : Set X))).exists_bound_of_continuousOn
        hP'.continuousOn
  have hi (s : ℝ) : Integrable (P s) μ :=
    (hP.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi' (s : ℝ) : Integrable (P' s) μ :=
    (hP'.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := P) (F' := P')
    (x₀ := t) (s := Set.Icc (t - 1) (t + 1)) (bound := fun _ => C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (hi s).aestronglyMeasurable)
    (hi t) (hi' t).aestronglyMeasurable
    (Eventually.of_forall fun q s hs => hC (s, q) ⟨hs, Set.mem_univ q⟩)
    (integrable_const C)
    (Eventually.of_forall fun q s _ => hderiv s q)).2

end ThetaGlobal.GlobalCompactPeriod
