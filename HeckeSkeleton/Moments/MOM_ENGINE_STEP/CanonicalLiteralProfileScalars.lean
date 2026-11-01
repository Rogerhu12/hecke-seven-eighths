import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds

/-!
# The exact scalar costs in the actual two-stage profiles

The inverse norm and both Mellin powers give one fixed power of the
profile variable. The remaining scale factors are displayed separately
at each original occurrence. In particular the two plain factors are
not replaced by their maximum: their product has the original centered
scale cancellation. The actual first common scalar and pool scalar
remain explicit complex factors.

The positive reciprocal balance below has an exact product identity.
It is an input to an equality-preserving atom-table construction, not
an assertion that the existing table was already balanced.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralProfileScalars

def exponent (δ₁ δ₂ : ℝ) : ℝ := -1 + δ₁ + δ₂

/-- The scale of the original Gauss denominator and the scale of the
selected centered rectangle need not agree. -/
def plainFactor (gaussScale profileScale δ₁ δ₂ : ℝ) : ℝ :=
  Real.sqrt gaussScale * profileScale ^ exponent δ₁ δ₂

theorem plainFactor_pos {G N : ℝ} (hG : 0 < G) (hN : 0 < N) (δ₁ δ₂ : ℝ) :
    0 < plainFactor G N δ₁ δ₂ :=
  mul_pos (Real.sqrt_pos.mpr hG) (Real.rpow_pos_of_pos hN _)

theorem normPower_product {N y : ℝ} (hN : 0 < N) (hy : 0 < y) (δ₁ δ₂ : ℝ) :
    ((N * y) ^ (-1 : ℝ) : ℂ) * ((N * y) ^ δ₁ : ℂ) * ((N * y) ^ δ₂ : ℂ) =
      (N ^ exponent δ₁ δ₂ : ℂ) * (y ^ exponent δ₁ δ₂ : ℂ) := by
  have h : (N * y) ^ (-1 : ℝ) * (N * y) ^ δ₁ * (N * y) ^ δ₂ =
      N ^ exponent δ₁ δ₂ * y ^ exponent δ₁ δ₂ := by
    rw [← Real.rpow_add (mul_pos hN hy), ← Real.rpow_add (mul_pos hN hy),
      Real.mul_rpow hN.le hy.le] <;> rfl
  exact_mod_cast h

theorem plainFactor_product {G₁ G₂ N₁ N₂ : ℝ}
    (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (δ₁ δ₂ : ℝ) :
    plainFactor G₁ N₁ δ₁ δ₂ * plainFactor G₂ N₂ δ₁ δ₂ =
      Real.sqrt (G₁ * G₂) * (N₁ * N₂) ^ exponent δ₁ δ₂ := by
  rw [Real.sqrt_mul hG₁.le, Real.mul_rpow hN₁.le hN₂.le]
  unfold plainFactor
  ring

/-- The two rectangle scales are compared through their product,
never by separate upper bounds on the comparison scales. -/
theorem plainFactor_product_of_equal_product {G₁ G₂ N₁ N₂ : ℝ}
    (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (heq : N₁ * N₂ = G₁ * G₂) (δ₁ δ₂ : ℝ) :
    plainFactor G₁ N₁ δ₁ δ₂ * plainFactor G₂ N₂ δ₁ δ₂ =
      (G₁ * G₂) ^ (-1 / 2 + δ₁ + δ₂) := by
  rw [plainFactor_product hG₁ hG₂ hN₁ hN₂, heq, Real.sqrt_eq_rpow,
    ← Real.rpow_add (mul_pos hG₁ hG₂)]
  congr 1
  unfold exponent
  ring

/-- This is a positive scalar even when either original complex
profile or the common frozen scalar vanishes. -/
def balance (left right : ℝ) : ℝ := Real.sqrt right / Real.sqrt left

theorem balance_pos {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    0 < balance left right := div_pos (Real.sqrt_pos.mpr hr) (Real.sqrt_pos.mpr hl)

theorem balance_mul_left {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    balance left right * left = Real.sqrt (left * right) := by
  rw [balance, div_mul_eq_mul_div, Real.sqrt_mul hl.le]
  apply (div_eq_iff (Real.sqrt_pos.mpr hl).ne').2
  conv_lhs => rw [← Real.sq_sqrt hl.le]
  ring

theorem right_div_balance {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    right / balance left right = Real.sqrt (left * right) := by
  rw [balance, div_div_eq_mul_div, Real.sqrt_mul hl.le]
  apply (div_eq_iff (Real.sqrt_pos.mpr hr).ne').2
  conv_lhs => rw [← Real.sq_sqrt hr.le]
  ring

theorem balance_preserves_product {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    (balance left right * left) * (right / balance left right) = left * right := by
  rw [balance_mul_left hl hr, right_div_balance hl hr,
    Real.mul_self_sqrt (mul_pos hl hr).le]

end CanonicalLiteralProfileScalars

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

theorem extract_scale_product (r : Bool)
    (h : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false) :
    (d.extract b).scale₁ r * (d.extract b).scale₂ r =
      (d.extract b).scale₁ false * (d.extract b).scale₂ false := by
  change d.scale₁ r / idealNorm K b.plainDivisor₁ *
      (d.scale₂ r / idealNorm K b.plainDivisor₂) =
    d.scale₁ false / idealNorm K b.plainDivisor₁ *
      (d.scale₂ false / idealNorm K b.plainDivisor₂)
  rw [div_mul_div_comm, div_mul_div_comm, h]

theorem extracted_plainFactor_product (r : Bool) (δ₁ δ₂ : ℝ)
    (h : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false) :
    CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂ *
      CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ =
      ((d.extract b).scale₁ false * (d.extract b).scale₂ false) ^
        (-1 / 2 + δ₁ + δ₂) :=
  CanonicalLiteralProfileScalars.plainFactor_product_of_equal_product
    ((d.extract b).scale₁_pos false) ((d.extract b).scale₂_pos false)
    ((d.extract b).scale₁_pos r) ((d.extract b).scale₂_pos r)
    (d.extract_scale_product b r h) δ₁ δ₂

namespace ProfileData

variable {d} (W : d.ProfileData)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

/-- Literal left profile, with both fixed complex scalars kept
outside the positive per-occurrence factor. -/
theorem secondInput_left_shape (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ) {y : ℝ} (hy : 0 < y) :
    ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).left r).profile u time y =
      (d.commonScalar b *
        (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) power.val firstElement)) *
        (CanonicalLiteralProfileScalars.plainFactor
          ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂ : ℂ) *
        ((W.left r).profile u time y *
          (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
  change ((((((W.left r).profile u time y * d.commonScalar b) *
      (Real.sqrt ((d.extract b).scale₁ false) : ℂ)) *
      (((d.extract b).scale₁ r * y) ^ (-1 : ℝ) : ℂ)) *
      (((d.extract b).scale₁ r * y) ^ δ₁ : ℂ)) *
      (((d.extract b).scale₁ r * y) ^ δ₂ : ℂ)) *
      (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) power.val firstElement) = _
  have hp := CanonicalLiteralProfileScalars.normPower_product
    ((d.extract b).scale₁_pos r) hy δ₁ δ₂
  calc
    _ = (d.commonScalar b *
        (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) power.val firstElement)) *
        (Real.sqrt ((d.extract b).scale₁ false) : ℂ) * (W.left r).profile u time y *
        ((((d.extract b).scale₁ r * y) ^ (-1 : ℝ) : ℂ) *
          (((d.extract b).scale₁ r * y) ^ δ₁ : ℂ) *
          (((d.extract b).scale₁ r * y) ^ δ₂ : ℂ)) := by ring
    _ = _ := by rw [hp]; simp only [CanonicalLiteralProfileScalars.plainFactor,
      Complex.ofReal_mul]; ring

theorem secondInput_right_shape (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ) {y : ℝ} (hy : 0 < y) :
    ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).right r).profile u time y =
      (CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ : ℂ) *
        ((W.right r).profile u time y *
          (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
  change ((((W.right r).profile u time y *
      (Real.sqrt ((d.extract b).scale₂ false) : ℂ)) *
      (((d.extract b).scale₂ r * y) ^ (-1 : ℝ) : ℂ)) *
      (((d.extract b).scale₂ r * y) ^ δ₁ : ℂ)) *
      (((d.extract b).scale₂ r * y) ^ δ₂ : ℂ) = _
  have hp := CanonicalLiteralProfileScalars.normPower_product
    ((d.extract b).scale₂_pos r) hy δ₁ δ₂
  calc
    _ = (Real.sqrt ((d.extract b).scale₂ false) : ℂ) * (W.right r).profile u time y *
        ((((d.extract b).scale₂ r * y) ^ (-1 : ℝ) : ℂ) *
          (((d.extract b).scale₂ r * y) ^ δ₁ : ℂ) *
          (((d.extract b).scale₂ r * y) ^ δ₂ : ℂ)) := by ring
    _ = _ := by rw [hp]; simp only [CanonicalLiteralProfileScalars.plainFactor,
      Complex.ofReal_mul]; ring

theorem secondInput_slot_shape (j : Fin b.keep.card) (time : ℝ) {y : ℝ} (hy : 0 < y) :
    ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).slot j).profile time y =
      (CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).base ^ (d.extract b).length j)
        ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ) *
        ((W.slot (SlotRestriction.index b.keep j)).profile time y *
          (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
  change ((((W.slot (SlotRestriction.index b.keep j)).profile time y *
      (Real.sqrt ((d.extract b).base ^ (d.extract b).length j) : ℂ)) *
      ((((d.extract b).base ^ (d.extract b).length j) * y) ^ (-1 : ℝ) : ℂ)) *
      ((((d.extract b).base ^ (d.extract b).length j) * y) ^ δ₁ : ℂ)) *
      ((((d.extract b).base ^ (d.extract b).length j) * y) ^ δ₂ : ℂ) = _
  have hp := CanonicalLiteralProfileScalars.normPower_product
    (Real.rpow_pos_of_pos (zero_lt_one.trans (d.extract b).base_gt_one)
      ((d.extract b).length j)) hy δ₁ δ₂
  calc
    _ = (Real.sqrt ((d.extract b).base ^ (d.extract b).length j) : ℂ) *
        (W.slot (SlotRestriction.index b.keep j)).profile time y *
        (((((d.extract b).base ^ (d.extract b).length j) * y) ^ (-1 : ℝ) : ℂ) *
          ((((d.extract b).base ^ (d.extract b).length j) * y) ^ δ₁ : ℂ) *
          ((((d.extract b).base ^ (d.extract b).length j) * y) ^ δ₂ : ℂ)) := by ring
    _ = _ := by rw [hp]; simp only [CanonicalLiteralProfileScalars.plainFactor,
      Complex.ofReal_mul]; ring

end ProfileData
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralProfileScalars.plainFactor_product_of_equal_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralProfileScalars.balance_preserves_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.extracted_plainFactor_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.secondInput_left_shape
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.secondInput_right_shape
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.secondInput_slot_shape
