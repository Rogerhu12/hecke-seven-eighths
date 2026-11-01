import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPlainBalance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileScalars
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScaleProduct

/-!
# Extract the actual positive factors of every original profile

The two logarithmic transforms leave positive scale factors in the two
plain profiles and in each prime occurrence. Their product must be paid
in the original row scalar before constructing normalized children.

This file divides each individual profile by its own positive factor.
The original finite supports, norm scales, characters, Gauss normalizer
and Fourier locations are unchanged. Each rectangle identity is proved
before summation. Centering uses only the equality of the two products;
the absent ordinary comparison rectangle remains exactly zero.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralProfileFactorExtraction

variable {k : ℕ}

def product (left right : Bool → ℝ) (slot : Fin k → ℝ) (r : Bool) : ℝ :=
  left r * right r * ∏ i, slot i

theorem product_pos (left right : Bool → ℝ) (slot : Fin k → ℝ)
    (hleft : ∀ r, 0 < left r) (hright : ∀ r, 0 < right r)
    (hslot : ∀ i, 0 < slot i) (r : Bool) :
    0 < product left right slot r :=
  mul_pos (mul_pos (hleft r) (hright r))
    (Finset.prod_pos fun i _ => hslot i)

end CanonicalLiteralProfileFactorExtraction

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : Atoms (K := K) k)

/-- Every original occurrence is divided by its own fixed positive
factor. No new norm scale or support is selected. -/
def divideProfileFactors (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * (left r : ℂ)⁻¹
    rightWeight := fun r I => d.rightWeight r I * (right r : ℂ)⁻¹
    slotWeight := fun i p => d.slotWeight i p * (slot i : ℂ)⁻¹ }

@[simp] theorem divideProfileFactors_characters
    (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    (d.divideProfileFactors left right slot).characters = d.characters := rfl

@[simp] theorem divideProfileFactors_normalizer
    (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    (d.divideProfileFactors left right slot).normalizer = d.normalizer := rfl

theorem divideProfileFactors_rectangleLeftWeight
    (left right : Bool → ℝ) (slot : Fin k → ℝ) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.divideProfileFactors left right slot).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * (left r : ℂ)⁻¹ := by
  unfold rectangleLeftWeight divideProfileFactors
  split_ifs <;> simp only [zero_mul]

/-- Literal coefficient identity, including all original zero-extended
characters and every repeated prime occurrence. -/
theorem divideProfileFactors_term
    (left right : Bool → ℝ) (slot : Fin k → ℝ)
    (r : Bool) (i : AllocationColumn K k) :
    (d.divideProfileFactors left right slot).term r i =
      d.term r i *
        (CanonicalLiteralProfileFactorExtraction.product left right slot r : ℂ)⁻¹ := by
  have he := CanonicalLiteralTransforms.bare_mul_weights d.characters
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r)
    (fun _ => (left r : ℂ)⁻¹) (fun _ => (right r : ℂ)⁻¹)
    d.slotWeight (fun j _ => (slot j : ℂ)⁻¹) i
  have hw := funext (d.divideProfileFactors_rectangleLeftWeight left right slot r)
  have hp : (left r : ℂ)⁻¹ * (right r : ℂ)⁻¹ * (∏ j, (slot j : ℂ)⁻¹) =
      (CanonicalLiteralProfileFactorExtraction.product left right slot r : ℂ)⁻¹ := by
    simp only [CanonicalLiteralProfileFactorExtraction.product, Complex.ofReal_mul,
      Complex.ofReal_prod, mul_inv_rev, Finset.prod_inv_distrib]
    ring
  unfold term
  rw [hw]
  change d.normalizer * rawBareSourceCoefficient d.characters
      (d.scale₁ r) (d.scale₂ r) d.base d.length
      (fun I => d.rectangleLeftWeight r I * (left r : ℂ)⁻¹)
      (fun I => d.rightWeight r I * (right r : ℂ)⁻¹)
      (fun j p => d.slotWeight j p * (slot j : ℂ)⁻¹) i = _
  rw [he, hp]
  ring

theorem term_eq_profileFactor_mul
    (left right : Bool → ℝ) (slot : Fin k → ℝ)
    (hleft : ∀ r, 0 < left r) (hright : ∀ r, 0 < right r)
    (hslot : ∀ i, 0 < slot i) (r : Bool) (i : AllocationColumn K k) :
    d.term r i =
      (CanonicalLiteralProfileFactorExtraction.product left right slot r : ℂ) *
        (d.divideProfileFactors left right slot).term r i := by
  have hp : (CanonicalLiteralProfileFactorExtraction.product left right slot r : ℂ) ≠ 0 := by
    exact_mod_cast (CanonicalLiteralProfileFactorExtraction.product_pos
      left right slot hleft hright hslot r).ne'
  rw [d.divideProfileFactors_term]
  calc
    _ = d.term r i *
        ((CanonicalLiteralProfileFactorExtraction.product left right slot r : ℂ) *
          (CanonicalLiteralProfileFactorExtraction.product left right slot r : ℂ)⁻¹) := by
      rw [mul_inv_cancel₀ hp, mul_one]
    _ = _ := by ring

/-- Centering keeps one scalar for the complete coefficient. For an
ordinary source no comparison-scale identity is needed. -/
theorem whole_eq_profileFactor_mul
    (left right : Bool → ℝ) (slot : Fin k → ℝ)
    (hleft : ∀ r, 0 < left r) (hright : ∀ r, 0 < right r)
    (hslot : ∀ i, 0 < slot i)
    (hcentered : d.centered = true → left true * right true = left false * right false)
    (i : AllocationColumn K k) :
    d.whole i =
      (CanonicalLiteralProfileFactorExtraction.product left right slot false : ℂ) *
        (d.divideProfileFactors left right slot).whole i := by
  cases hc : d.centered with
  | false =>
      have hz : d.term true i = 0 := by
        simp only [d.term_true i, hc, Bool.false_eq_true, if_false]
      have hz' : (d.divideProfileFactors left right slot).term true i = 0 := by
        rw [d.divideProfileFactors_term, hz, zero_mul]
      change d.term false i - d.term true i = _ *
        ((d.divideProfileFactors left right slot).term false i -
          (d.divideProfileFactors left right slot).term true i)
      rw [hz, hz', sub_zero, sub_zero]
      exact d.term_eq_profileFactor_mul left right slot hleft hright hslot false i
  | true =>
      have hp : CanonicalLiteralProfileFactorExtraction.product left right slot true =
          CanonicalLiteralProfileFactorExtraction.product left right slot false := by
        unfold CanonicalLiteralProfileFactorExtraction.product
        rw [hcentered hc]
      change d.term false i - d.term true i = _ *
        ((d.divideProfileFactors left right slot).term false i -
          (d.divideProfileFactors left right slot).term true i)
      rw [d.term_eq_profileFactor_mul left right slot hleft hright hslot false i,
        d.term_eq_profileFactor_mul left right slot hleft hright hslot true i, hp,
        mul_sub]

/-- Support extraction keeps the original factor of every retained
occurrence; it does not recompute it from a new quotient scale. -/
theorem divideProfileFactors_extract
    (left right : Bool → ℝ) (slot : Fin k → ℝ)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.divideProfileFactors left right slot).extract b =
      (d.extract b).divideProfileFactors left right
        (fun i => slot (SlotRestriction.index b.keep i)) := rfl

/-- Concentrate the product in the first plain profile, so the
existing constant-extraction operation can move it to the row weight.
The complete original coefficient is preserved below. -/
def redistributeProfileFactors (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    Atoms (K := K) k :=
  (d.divideProfileFactors left right slot).scale
    (CanonicalLiteralProfileFactorExtraction.product left right slot false : ℂ)

theorem redistributeProfileFactors_whole
    (left right : Bool → ℝ) (slot : Fin k → ℝ)
    (hleft : ∀ r, 0 < left r) (hright : ∀ r, 0 < right r)
    (hslot : ∀ i, 0 < slot i)
    (hcentered : d.centered = true → left true * right true = left false * right false)
    (i : AllocationColumn K k) :
    (d.redistributeProfileFactors left right slot).whole i = d.whole i := by
  rw [redistributeProfileFactors, scale_whole]
  exact (d.whole_eq_profileFactor_mul left right slot hleft hright hslot hcentered i).symm

namespace ProfileData

variable {d} (W : d.ProfileData)

def divideProfileFactors (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    (d.divideProfileFactors left right slot).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest (W.left r) (fun _ => (left r : ℂ)⁻¹)
  right r := CanonicalLiteralProfileData.mulIdealTest (W.right r) (fun _ => (right r : ℂ)⁻¹)
  slot i := CanonicalLiteralProfileData.mulPrimeWindow (W.slot i) (fun _ => (slot i : ℂ)⁻¹)
  slot_length := W.slot_length
  left_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.left_positive r)
  right_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.right_positive r)
  slot_positive i := CanonicalLiteralProfileData.mulPrimeWindow_positive _ _ (W.slot_positive i)
  left_frozen r u t y := congrArg (fun z => z * (left r : ℂ)⁻¹) (W.left_frozen r u t y)
  right_frozen r u t y := congrArg (fun z => z * (right r : ℂ)⁻¹) (W.right_frozen r u t y)
  slot_frozen i t y := congrArg (fun z => z * (slot i : ℂ)⁻¹) (W.slot_frozen i t y)
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / d.scale₁ r) * (left r : ℂ)⁻¹ = _
    rw [W.left_eval, d.divideProfileFactors_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t (idealNorm K I / d.scale₂ r) * (right r : ℂ)⁻¹ = _
    rw [W.right_eval] <;> rfl
  slot_eval i t p := by
    change (W.slot i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length i) *
      (slot i : ℂ)⁻¹ = _
    rw [W.slot_eval] <;> rfl

def redistributeProfileFactors (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    (d.redistributeProfileFactors left right slot).ProfileData :=
  (W.divideProfileFactors left right slot).scale
    (CanonicalLiteralProfileFactorExtraction.product left right slot false : ℂ)

end ProfileData

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def divideProfileFactors (W : d.SupportData excluded)
    (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    (d.divideProfileFactors left right slot).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.divideProfileFactors_rectangleLeftWeight left right slot r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem i p hp havoid := W.slot_mem i p (left_ne_zero_of_mul hp) havoid

def redistributeProfileFactors (W : d.SupportData excluded)
    (left right : Bool → ℝ) (slot : Fin k → ℝ) :
    (d.redistributeProfileFactors left right slot).SupportData excluded :=
  (W.divideProfileFactors left right slot).scale
    (CanonicalLiteralProfileFactorExtraction.product left right slot false : ℂ)

end SupportData

section TwoStageFactors

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

def twoStageProfileLeftFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂

def twoStageProfileRightFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂

def twoStageProfileSlotFactor (δ₁ δ₂ : ℝ) (i : Fin b.keep.card) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).base ^ (d.extract b).length i)
    ((d.extract b).base ^ (d.extract b).length i) δ₁ δ₂

theorem twoStageProfileLeftFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) :
    0 < d.twoStageProfileLeftFactor b δ₁ δ₂ r :=
  CanonicalLiteralProfileScalars.plainFactor_pos
    ((d.extract b).scale₁_pos false) ((d.extract b).scale₁_pos r) δ₁ δ₂

theorem twoStageProfileRightFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) :
    0 < d.twoStageProfileRightFactor b δ₁ δ₂ r :=
  CanonicalLiteralProfileScalars.plainFactor_pos
    ((d.extract b).scale₂_pos false) ((d.extract b).scale₂_pos r) δ₁ δ₂

theorem twoStageProfileSlotFactor_pos (δ₁ δ₂ : ℝ) (i : Fin b.keep.card) :
    0 < d.twoStageProfileSlotFactor b δ₁ δ₂ i :=
  CanonicalLiteralProfileScalars.plainFactor_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _) δ₁ δ₂

/-- The factor uses the complete scale product after the first
extraction, before the second common-support split. -/
def twoStageProfileFactor (δ₁ δ₂ : ℝ) : ℝ :=
  (d.extract b).scaleProduct false ^ (-1 / 2 + δ₁ + δ₂)

theorem twoStageProfileFactor_pos (δ₁ δ₂ : ℝ) :
    0 < d.twoStageProfileFactor b δ₁ δ₂ :=
  Real.rpow_pos_of_pos ((d.extract b).scaleProduct_pos false) _

theorem twoStageProfileSlotFactor_eq (δ₁ δ₂ : ℝ) (i : Fin b.keep.card) :
    d.twoStageProfileSlotFactor b δ₁ δ₂ i =
      ((d.extract b).base ^ (d.extract b).length i) ^ (-1 / 2 + δ₁ + δ₂) := by
  unfold twoStageProfileSlotFactor CanonicalLiteralProfileScalars.plainFactor
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)]
  congr 1
  unfold CanonicalLiteralProfileScalars.exponent
  ring

/-- The product is computed from the original per-occurrence factors.
In particular no final polynomial equality is a hypothesis. -/
theorem twoStageProfileFactor_product (δ₁ δ₂ : ℝ) (r : Bool)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false) :
    CanonicalLiteralProfileFactorExtraction.product
        (d.twoStageProfileLeftFactor b δ₁ δ₂)
        (d.twoStageProfileRightFactor b δ₁ δ₂)
        (d.twoStageProfileSlotFactor b δ₁ δ₂) r =
      d.twoStageProfileFactor b δ₁ δ₂ := by
  unfold CanonicalLiteralProfileFactorExtraction.product
    twoStageProfileLeftFactor twoStageProfileRightFactor
  rw [d.extracted_plainFactor_product b r δ₁ δ₂ hproduct]
  simp_rw [d.twoStageProfileSlotFactor_eq b δ₁ δ₂]
  rw [Real.finsetProd_rpow Finset.univ _
    (fun i _ => Real.rpow_nonneg (zero_le_one.trans d.base_gt_one.le) _) _]
  exact (Real.mul_rpow
    (mul_pos ((d.extract b).scale₁_pos false) ((d.extract b).scale₂_pos false)).le
    (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (zero_le_one.trans d.base_gt_one.le) _)
    (-1 / 2 + δ₁ + δ₂)).symm

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)

/-- Divide the literal two-stage profiles before either side's
normalized children are chosen. The original first common and pool
scalar has not yet been removed from its first plain profile. -/
def factorizedSecondInput (δ₁ δ₂ : ℝ) : Atoms (K := K) b.keep.card :=
  (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).divideProfileFactors
      (d.twoStageProfileLeftFactor b δ₁ δ₂)
      (d.twoStageProfileRightFactor b δ₁ δ₂)
      (d.twoStageProfileSlotFactor b δ₁ δ₂)

/-- This factorization has the same complete coefficient as the
actual second input. Its two first scalar factors can now be extracted
together, before constructing either normalized side. -/
def redistributedSecondInput (δ₁ δ₂ : ℝ) : Atoms (K := K) b.keep.card :=
  (d.factorizedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
      (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)

/-- The same complete centered source exposes its missing positive
scale factor. For an ordinary source the comparison term is already
zero and no equality for its arbitrary comparison scales is required. -/
theorem secondInput_eq_profileFactor_mul (δ₁ δ₂ : ℝ)
    (hproduct : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (i : AllocationColumn K b.keep.card) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i =
      (d.twoStageProfileFactor b δ₁ δ₂ : ℂ) *
        (d.factorizedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
          firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i := by
  have hc : d.centered = true →
      d.twoStageProfileLeftFactor b δ₁ δ₂ true *
        d.twoStageProfileRightFactor b δ₁ δ₂ true =
      d.twoStageProfileLeftFactor b δ₁ δ₂ false *
        d.twoStageProfileRightFactor b δ₁ δ₂ false := by
    intro h
    exact (d.extracted_plainFactor_product b true δ₁ δ₂ (hproduct h)).trans
      (d.extracted_plainFactor_product b false δ₁ δ₂ rfl).symm
  have he := (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole_eq_profileFactor_mul
      (d.twoStageProfileLeftFactor b δ₁ δ₂)
      (d.twoStageProfileRightFactor b δ₁ δ₂)
      (d.twoStageProfileSlotFactor b δ₁ δ₂)
      (d.twoStageProfileLeftFactor_pos b δ₁ δ₂)
      (d.twoStageProfileRightFactor_pos b δ₁ δ₂)
      (d.twoStageProfileSlotFactor_pos b δ₁ δ₂) hc i
  simpa only [d.twoStageProfileFactor_product b δ₁ δ₂ false rfl] using he

theorem redistributedSecondInput_whole (δ₁ δ₂ : ℝ)
    (hproduct : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (i : AllocationColumn K b.keep.card) :
    (d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i =
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i := by
  rw [redistributedSecondInput, scale_whole]
  exact (d.secondInput_eq_profileFactor_mul b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hproduct i).symm

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- Actual individual test functions for the factorized source. Their
finite supports and frozen row/time dependence are constructed above. -/
def factorizedSecondInput (δ₁ δ₂ : ℝ) :
    (d.factorizedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).ProfileData :=
  (W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).divideProfileFactors
      (d.twoStageProfileLeftFactor b δ₁ δ₂)
      (d.twoStageProfileRightFactor b δ₁ δ₂)
      (d.twoStageProfileSlotFactor b δ₁ δ₂)

def redistributedSecondInput (δ₁ δ₂ : ℝ) :
    (d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).ProfileData :=
  (W.factorizedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
      (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)

end ProfileData

end TwoStageFactors
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.divideProfileFactors_term
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.term_eq_profileFactor_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.whole_eq_profileFactor_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.divideProfileFactors_extract
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.redistributeProfileFactors_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.twoStageProfileFactor_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_eq_profileFactor_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.redistributedSecondInput_whole
