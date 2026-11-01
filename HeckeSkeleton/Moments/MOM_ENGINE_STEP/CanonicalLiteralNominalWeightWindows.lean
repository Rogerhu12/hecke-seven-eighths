import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalWeightWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCapacityLengths

/-!
# Original table windows in the same nominal coordinates

Only the identity of the original complete first extraction ideal and
the parent's total length are used. The source constructors supply the
window record. No capacity or normalized child is chosen in this step.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : Atoms (K := K) k)

@[simp] theorem onAtlas_centered_eq {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (h : k = T.slotCount) :
    (d.onAtlas T h).centered = d.centered := by
  cases h
  rfl

namespace OriginalWeightWindows

variable {d : Atoms (K := K) k} {centered : Bool} {cap : ℕ}
variable {bound annulus Z total : ℝ} {firstFrozen : Ideal (𝓞 K)}
variable (W : d.OriginalWeightWindows centered cap bound annulus Z total firstFrozen)
variable {a : RealParameters} {step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (hfirst : G.literalFirstExtraction.val = firstFrozen)
variable (htotal : total = a.n₁ + a.n₂ + a.z)

include W hfirst htotal

/-- The scale bound remains restricted to a rectangle present in the
actual original source. -/
theorem nominal_scale (hcentered : d.centered = centered) (r : Bool)
    (hr : r = false ∨ d.centered = true) :
    d.scaleProduct r * (Ideal.absNorm G.literalFirstExtraction.val : ℝ) ≤
      annulus ^ cap * Z ^ (a.n₁ + a.n₂ + a.z) := by
  rw [hcentered] at hr
  simpa only [hfirst, htotal] using W.present_scale r hr

/-- The complete first frozen norm is precisely the original
`c + w` contribution, including the actual pool power. -/
theorem nominal_gauss :
    Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ d.gaussScale := by
  have he : total - idealLogLength Z firstFrozen =
      G.skeleton.A - G.skeleton.c - G.skeleton.w := by
    rw [← hfirst, G.literalFirstExtraction_length, htotal]
    change G.skeleton.A - (G.skeleton.c + G.skeleton.w) = _
    ring
  simpa only [he] using W.gauss_lower

end OriginalWeightWindows
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.OriginalWeightWindows.nominal_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.OriginalWeightWindows.nominal_gauss
