import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveProfileBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllSideClipping

set_option linter.unusedSectionVars false

/-!
# A fixed bound for the same computed literal profile radius

The coefficient is assembled in the order actually used to construct
the representatives: the scalar-free balanced profile, its exact
Fourier multiplier, and its two actual clipping dilations. For an
active side the original ideal summand supplies both required scale
lower bounds. This compares the already chosen radius with a constant
depending only on the original profile bound, annulus, fixed tilts,
direction and finite orders; it does not replace that radius.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralRadiusBound

def combined (B Cshape Cfourier factor clipping : ℝ) : ℝ :=
  clipping * (1 + (B + B * Cshape * (1 + factor)) * (1 + Cfourier))

theorem combined_nonneg {B Cshape Cfourier factor clipping : ℝ}
    (hB : 0 ≤ B) (hshape : 0 ≤ Cshape) (hfourier : 0 ≤ Cfourier)
    (hfactor : 0 ≤ factor) (hclipping : 0 ≤ clipping) :
    0 ≤ combined B Cshape Cfourier factor clipping := by
  sorry

theorem combined_mono {B Cshape Cfourier factor factor' clipping clipping' : ℝ}
    (hB : 0 ≤ B) (hshape : 0 ≤ Cshape) (hfourier : 0 ≤ Cfourier)
    (hfactor : 0 ≤ factor) (hfactor' : factor ≤ factor')
    (hclipping : clipping ≤ clipping') (hclipping' : 0 ≤ clipping') :
    combined B Cshape Cfourier factor clipping ≤
      combined B Cshape Cfourier factor' clipping' := by
  sorry

def shapeCoefficient (lo hi : ℝ) (hlo : 0 < lo) (δ₁ δ₂ : ℝ)
    (s : Finset (ℕ × ℕ)) : ℝ :=
  CanonicalLogProfiles.shapeCoefficient (Set.Icc lo hi) isCompact_Icc
    (CanonicalLogProfiles.positiveAnnulus lo hi hlo)
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s)

def fourierCoefficient (lo hi : ℝ) (hlo : 0 < lo) (firstSign : ℝ)
    (s : Finset (ℕ × ℕ)) : ℝ :=
  CanonicalLiteralFourierWindows.coefficient (Set.Icc lo hi) isCompact_Icc
    (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign s

/-- No moving source, label, scale, rectangle or Fourier point enters
this coefficient. `B` is the original finite-profile bound. -/
def fixedCoefficient (B lo hi : ℝ) (hlo : 0 < lo) (δ₁ δ₂ firstSign : ℝ)
    (s : Finset (ℕ × ℕ)) : ℝ :=
  combined B (shapeCoefficient lo hi hlo δ₁ δ₂ s)
    (fourierCoefficient lo hi hlo firstSign s) (Real.sqrt hi)
    (1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s)

variable {K : Type} [Field K] [NumberField K] {k : ℕ} {ω ψ : HeckeCharacter K}

/-- The raw window here is the constructed value returned by the
literal profile constructors. Only genuine nonzero summands and the
two original quotient-scale identities enter the scale argument. -/
theorem actualCoefficient_le_fixed
    (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (r : Bool) (δ₁ δ₂ : ℝ) (child : MomentData K ω ψ) (parameters : RealParameters)
    (time B lo hi : ℝ) (hB : 0 ≤ B) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (firstSign : ℝ) (s : Finset (ℕ × ℕ))
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false)
    (I₁ I₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hscale₁ : d.base ^ parameters.n₁ = (d.extract b).scale₁ r / idealNorm K I₁)
    (hscale₂ : d.base ^ parameters.n₂ = (d.extract b).scale₂ r / idealNorm K I₂)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
    {rawBound : ℝ}
    (raw : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s child rawBound)
    (hrows : ∀ u ∈ pairedRows child parameters d.base, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy child parameters d.base time ≠ 0) :
    combined B (shapeCoefficient lo hi hlo δ₁ δ₂ s)
      (fourierCoefficient lo hi hlo firstSign s)
      (CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r)
      (CanonicalLiteralAllSideClipping.cost d.base parameters s) ≤
      fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s := by
  sorry

theorem radius_le_of_coefficient {B C : ℝ} (h : B ≤ C) (J₁ J₂ : ℕ) (ξ : ℝ × ℝ) :
    polynomialProfileRadius B J₁ J₂ ξ ≤ polynomialProfileRadius C J₁ J₂ ξ := by
  sorry

end CanonicalLiteralRadiusBound
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRadiusBound.actualCoefficient_le_fixed
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRadiusBound.radius_le_of_coefficient
