import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFactorFreeProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStripExistingBinding

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
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

/-- This coefficient is fixed before every original profile and table. -/
def coefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ₁ δ₂ : ℝ) (orders : Finset (ℕ × ℕ)) : ℝ :=
  1 + CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders orders)

theorem coefficient_one (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (δ₁ δ₂ : ℝ) (orders : Finset (ℕ × ℕ)) :
    1 ≤ coefficient window hcompact hpositive δ₁ δ₂ orders :=
  le_add_of_nonneg_right (CanonicalLogProfiles.shapeCoefficient_nonneg
    window hcompact hpositive _ _)

private theorem orders_mono (orders : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      (CanonicalLogProfiles.sourceOrders orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ :=
  Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    (fun p hp => Seminorm.le_finset_sup_apply (CanonicalLogProfiles.subset_sourceOrders orders hp))

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
  (seedProfiles.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
      (seed.secondInputScalar (σ := σ) b power firstElement δ₁ *
        (seed.twoStageProfileFactor b δ₁ δ₂ : ℂ))⁻¹

/-- The same computed model satisfies a fixed bound with no residual
factor. The original window, rather than a child seminorm bound, is the
input. The larger original orders are retained for later Fourier use. -/
theorem computed_sourceOrders_bounds :
    (∀ r, (CanonicalLogProfiles.sourceOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (T.model.left r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ r, (CanonicalLogProfiles.sourceOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (T.model.right r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ j, (CanonicalLogProfiles.sourceOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (T.model.slot j) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) := by
  let E := Q.literalOriginalSchwartzModel ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed
  have hb := Q.literalOriginalSchwartzModel_bound ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed hamplitude
  let Cshape := CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders orders)
  have hC : 0 ≤ Cshape := CanonicalLogProfiles.shapeCoefficient_nonneg
    window hcompact hpositive _ _
  have hlarge : Cshape * amplitude ≤
      coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hamplitude
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact (E.factorFree_left_bound (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      r (CanonicalLogProfiles.sourceOrders orders)).trans
        ((mul_le_mul_of_nonneg_left (hb.1 r) hC).trans hlarge)
  · intro r
    exact (E.factorFree_right_bound (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      r (CanonicalLogProfiles.sourceOrders orders)).trans
        ((mul_le_mul_of_nonneg_left (hb.2.1 r) hC).trans hlarge)
  · intro j
    exact (E.factorFree_slot_bound (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      j (CanonicalLogProfiles.sourceOrders orders)).trans
        ((mul_le_mul_of_nonneg_left (hb.2.2 (SlotRestriction.index b.keep j)) hC).trans hlarge)

/-- In particular the requested volume orders hold on these same
representatives. No new representative or normalization is chosen. -/
theorem computed_bounds :
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.model.left r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ r, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.model.right r) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) ∧
    (∀ j, orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.model.slot j) ≤
        coefficient window hcompact hpositive δ₁ δ₂ orders * amplitude) := by
  have h := computed_sourceOrders_bounds Q ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    reference href orders amplitude hamplitude original hreference ht hcompact hpositive
    hprime b power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂
  exact ⟨fun r => (orders_mono orders _).trans (h.1 r),
    fun r => (orders_mono orders _).trans (h.2.1 r),
    fun j => (orders_mono orders _).trans (h.2.2 j)⟩

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
      hfirst hpool hunit δ₁ δ₂).model = T.model := rfl

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
  have hraw := right_ne_zero_of_mul hne
  change rawBareSourceCoefficient d.characters (d.scale₁ r) (d.scale₂ r)
    d.base d.length (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i ≠ 0 at hraw
  dsimp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient] at hraw
  have hleft : d.rectangleLeftWeight r (sourceMomentIdeal i.1.1) ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hraw)))
  have hright : d.rightWeight r (sourceMomentIdeal i.1.2) ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul hraw)))
  rw [← W.left_eval r 1 0, E.left_eq] at hleft
  rw [← W.right_eval r 1 0, E.right_eq] at hright
  exact ⟨hleft, hright⟩

theorem term_scale_lower (hi : ℝ) (hhi : 0 < hi)
    (hwindow : window ⊆ Set.Iic hi) (r : Bool) (i : AllocationColumn K k)
    (hne : d.term r i ≠ 0) :
    1 / hi ≤ d.scale₁ r ∧ 1 / hi ≤ d.scale₂ r := by
  have hv := term_nonzero_profile_values E r i hne
  have hleft := hwindow (E.left_support r (subset_tsupport _ hv.1))
  have hright := hwindow (E.right_support r (subset_tsupport _ hv.2))
  constructor
  · apply (div_le_iff₀ hhi).mpr
    have h := (one_le_idealNorm K (sourceMomentIdeal i.1.1)).trans
      ((div_le_iff₀ (d.scale₁_pos r)).mp hleft)
    simpa only [mul_comm] using h
  · apply (div_le_iff₀ hhi).mpr
    have h := (one_le_idealNorm K (sourceMomentIdeal i.1.2)).trans
      ((div_le_iff₀ (d.scale₂_pos r)).mp hright)
    simpa only [mul_comm] using h

/-- A whole centered column may be active in either rectangle. Their
original equal scale products transfer the resulting lower bound. -/
theorem whole_scale_product_lower (hi : ℝ) (hhi : 0 < hi)
    (hwindow : window ⊆ Set.Iic hi)
    (hproduct : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (i : AllocationColumn K k) (hne : d.whole i ≠ 0) :
    hi ^ (-2 : ℝ) ≤ d.scale₁ false * d.scale₂ false := by
  have hterm : ∃ r, d.term r i ≠ 0 := by
    by_cases hfalse : d.term false i = 0
    · refine ⟨true, ?_⟩
      intro htrue
      exact hne (by simp only [CanonicalLiteralRectangles.Atoms.whole, hfalse, htrue, sub_self])
    · exact ⟨false, hfalse⟩
  obtain ⟨r, hr⟩ := hterm
  have hlower := term_scale_lower E hi hhi hwindow r i hr
  have heq : hi ^ (-2 : ℝ) = (1 / hi) * (1 / hi) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hhi.le, Real.rpow_two]
    simp only [pow_two, one_div, mul_inv_rev]
  have h := mul_le_mul hlower.1 hlower.2 (div_nonneg zero_le_one hhi.le) (d.scale₁_pos r).le
  rw [← heq] at h
  cases r
  · exact h
  · have hc : d.centered = true := by
      cases he : d.centered
      · have hz : d.term true i = 0 := by simp only [d.term_true, he, Bool.false_eq_true, if_false]
        exact (hr hz).elim
      · exact he
    exact h.trans_eq (hproduct hc)

end WholeSupport

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.computed_sourceOrders_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.computed_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.uniformComputedProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.uniformComputedProfiles_model
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalProfileWindow.whole_scale_product_lower
