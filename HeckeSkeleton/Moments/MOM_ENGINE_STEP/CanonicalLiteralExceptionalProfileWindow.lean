import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStripExistingBinding

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Original profile windows on the actual exceptional atom model

The factor-free model has a stronger estimate than the scale-dependent
coefficient stored in the ordinary normalization interface. Its actual
representatives are the original profiles multiplied by one fixed real
power. The bound below applies to precisely the existing computed model,
then transports through the original extraction, atlas and mask steps.

The numerical coefficient is fixed by the original compact support,
the two fixed tilts and the requested finite orders. It does not contain
a source, Fourier mode, common ideal, profile or central scale.

Separately, a nonzero whole coefficient provides a true plain-scale
lower bound: one of its two original terms is nonzero, and its two
individual profiles are supported in the original annulus. This does
not require a nonzero ordinary paired energy.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

/-- This coefficient is fixed before every original profile and table. -/
def coefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ₁ δ₂ : ℝ) (orders : Finset (ℕ × ℕ)) : ℝ :=
  1 + CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders orders)

theorem coefficient_one (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ₁ δ₂ : ℝ) (orders : Finset (ℕ × ℕ)) :
    1 ≤ coefficient window hcompact hpositive δ₁ δ₂ orders := by
  sorry

private theorem orders_mono (orders : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      (CanonicalLogProfiles.sourceOrders orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  sorry

section OriginalFactorFree

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (recipe : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : (data ξ).allowedRow reference)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (orders : Finset (ℕ × ℕ)) (amplitude : ℝ) (hamplitude : 0 ≤ amplitude)
variable (original : RawProfileWindow rowDomain heightDomain window
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
    (data ξ) amplitude)
variable (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (hprime : ∀ j, Function.support (original.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch
  (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
  (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
  (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

local notation "T" => Q.literalFactorFreeComputedProfiles ξ recipe a Z t Y₁ Y₂ centered
  hZ hY₁ hY₂ reference href orders amplitude hamplitude original hreference ht
  hcompact hpositive hprime b power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂

local notation "seed" => Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "seedProfiles" => Q.literalOriginalProfileDataOfWindow ξ recipe a Z t Y₁ Y₂
  centered hZ hY₁ hY₂ reference href original hreference ht hpositive
local notation "fixedProfiles" =>
  ((seedProfiles).redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
      ((seed).secondInputScalar (σ := σ) b power firstElement δ₁ *
        ((seed).twoStageProfileFactor b δ₁ δ₂ : ℂ))⁻¹

/-- The same computed model satisfies a fixed bound with no residual
factor. The original window, rather than a child seminorm bound, is the
input. The larger original orders are retained for later Fourier use. -/
theorem computed_sourceOrders_bounds :
    (∀ r, (CanonicalLogProfiles.sourceOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) ((T).model.left r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ r, (CanonicalLogProfiles.sourceOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) ((T).model.right r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ j, (CanonicalLogProfiles.sourceOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) ((T).model.slot j) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) := by
  sorry

/-- In particular the requested volume orders hold on these same
representatives. No new representative or normalization is chosen. -/
theorem computed_bounds :
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((T).model.left r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((T).model.right r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ j, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((T).model.slot j) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) := by
  sorry

/-- A certificate for the same model with its proved uniform numerical
bound. Existing profile transports can consume this certificate. It
does not reconstruct a normalized child or change its selected radius. -/
def uniformComputedProfiles :
    CanonicalLiteralFullKappaInput.ComputedProfiles fixedProfiles window orders amplitude := by
  have hC := coefficient_one window hcompact hpositive δ₁ δ₂ orders
  have h := computed_sourceOrders_bounds Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href orders amplitude hamplitude original hreference ht hcompact hpositive
    hprime b power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂
  refine
    { T with
      bound := fun _ => coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude
      bound_nonneg := fun _ => mul_nonneg (zero_le_one.trans hC) hamplitude
      original_bound := ?_
      left_bound := h.1
      right_bound := h.2.1
      slot_bound := fun _ j => h.2.2 j }
  intro r
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hamplitude

theorem uniformComputedProfiles_model :
    (uniformComputedProfiles Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
      orders amplitude hamplitude original hreference ht hcompact hpositive hprime b
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂).model = (T).model := rfl

theorem uniformComputedProfiles_bound (r : Bool) :
    (uniformComputedProfiles Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
      orders amplitude hamplitude original hreference ht hcompact hpositive hprime b
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂).bound r =
      coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude := rfl

end OriginalFactorFree

section WholeSupport

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)

/-- Each nonzero original term exhibits two actual nonzero profile
values. Its character and central denominators need no lower bounds. -/
theorem term_nonzero_profile_values (r : Bool) (i : AllocationColumn K k)
    (hne : d.term r i ≠ 0) :
    E.left r (idealNorm K (sourceMomentIdeal i.1.1) / d.scale₁ r) ≠ 0 ∧
      E.right r (idealNorm K (sourceMomentIdeal i.1.2) / d.scale₂ r) ≠ 0 := by
  sorry

include E in
theorem term_scale_lower (hi : ℝ) (hhi : 0 < hi)
    (hwindow : window ⊆ Set.Iic hi) (r : Bool) (i : AllocationColumn K k)
    (hne : d.term r i ≠ 0) :
    1 / hi ≤ d.scale₁ r ∧ 1 / hi ≤ d.scale₂ r := by
  sorry

include E in
/-- A whole centered column may be active in either rectangle. Their
original equal scale products transfer the resulting lower bound. -/
theorem whole_scale_product_lower (hi : ℝ) (hhi : 0 < hi)
    (hwindow : window ⊆ Set.Iic hi)
    (hproduct : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (i : AllocationColumn K k) (hne : d.whole i ≠ 0) :
    hi ^ (-2 : ℝ) ≤ d.scale₁ false * d.scale₂ false := by
  sorry

end WholeSupport

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.computed_sourceOrders_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.computed_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.uniformComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.uniformComputedProfiles_model
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.whole_scale_product_lower
