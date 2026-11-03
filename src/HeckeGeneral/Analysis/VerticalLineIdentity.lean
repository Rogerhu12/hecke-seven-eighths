import HeckeGeneral.Analysis.MellinZeroDetector
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# From a vertical-line identity to an initial meromorphic germ

The line identity remains an explicit hypothesis. The first theorem uses
noncentral points on the line arbitrarily close to c and the meromorphic
identity principle. The second theorem applies it to the ACTUAL physical
Mellin integral, with general c>b (M uses c=2).
-/

noncomputable section

namespace HeckeGeneral.Analysis

open Filter Set
open scoped Topology

/-- Equality on a vertical line supplies equality of punctured germs at its
real central point. Values assigned at that central point are not used. -/
theorem meromorphic_germ_eq_of_verticalLine {f g : ℂ → ℂ} {c : ℝ}
    (hf : MeromorphicAt f (c : ℂ)) (hg : MeromorphicAt g (c : ℂ))
    (hline : ∀ t : ℝ,
      f ((c : ℂ) + (t : ℂ) * Complex.I) =
        g ((c : ℂ) + (t : ℂ) * Complex.I)) :
    f =ᶠ[𝓝[≠] (c : ℂ)] g := by
  apply (hf.frequently_eq_iff_eventuallyEq hg).mp
  apply Filter.frequently_iff.mpr
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
  have ht : 0 < ε / 2 := by linarith
  let z : ℂ := (c : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I
  have hzsub : z - (c : ℂ) = ((ε / 2 : ℝ) : ℂ) * Complex.I := by
    dsimp [z]
    ring
  have hzdist : dist z (c : ℂ) = ε / 2 := by
    rw [dist_eq_norm, hzsub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos ht]
  have hzball : z ∈ Metric.ball (c : ℂ) ε := by
    change dist z (c : ℂ) < ε
    rw [hzdist]
    linarith
  have hzne : z ≠ (c : ℂ) := by
    intro hz
    have him := congrArg Complex.im hz
    have hz₀ : ε / 2 = 0 := by simpa [z] using him
    linarith
  have hzpunctured : z ∈ ({(c : ℂ)} : Set ℂ)ᶜ := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzne
  refine ⟨z, hsub ⟨hzball, hzpunctured⟩, ?_⟩
  exact hline (ε / 2)

/-- A verified vertical-line Mellin product identity provides the one initial
germ required by the detector. Analytic continuation of the physical Mellin
integral follows from `PhysicalProbeBound`; the line identity itself is not
asserted or inferred from that growth bound. -/
theorem initialMellinDetectorIdentity_of_verticalLine
    {L H : ℂ → ℂ} {f : ℝ → ℂ} {b c : ℝ}
    (hL : MeromorphicOn L (rightHalfPlane b))
    (hf : PhysicalProbeBound f b)
    (hH : AnalyticOnNhd ℂ H (rightHalfPlane b))
    (hHne : ∀ s ∈ rightHalfPlane b, H s ≠ 0)
    (hbc : b < c)
    (hline : ∀ t : ℝ,
      L ((c : ℂ) + (t : ℂ) * Complex.I) *
        physicalMellin f ((c : ℂ) + (t : ℂ) * Complex.I) =
          H ((c : ℂ) + (t : ℂ) * Complex.I)) :
    InitialMellinDetectorIdentity L f H b := by
  have hc : (c : ℂ) ∈ rightHalfPlane b := by
    exact hbc
  refine ⟨hH, hHne, (c : ℂ), hc, ?_⟩
  exact meromorphic_germ_eq_of_verticalLine
    ((hL (c : ℂ) hc).mul ((physicalMellin_analyticOnNhd hf (c : ℂ) hc).meromorphicAt))
    ((hH (c : ℂ) hc).meromorphicAt) hline

end HeckeGeneral.Analysis
