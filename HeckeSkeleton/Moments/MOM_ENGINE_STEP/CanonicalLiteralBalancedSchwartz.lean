import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSchwartzProfiles

/-!
# Quantitative profiles after exact scalar extraction and balancing

The atom table is scaled by the inverse of its actual first common and
pool scalar, then balanced by positive reciprocal plain factors. The
two operations are the literal existing atom constructors. Even when
the extracted scalar is zero these representatives exist; its inverse
is then zero and the left profile vanishes. On a live source the
nonzero scalar is transferred to the original row weight separately.

The remaining seminorm costs contain the product of the two true plain
scale factors. Neither the removed complex scalar nor the ratio of the
centered scales enters their common normalization radius.
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

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralBalancedSchwartz

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

def leftFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂

def rightFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂

theorem leftFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < leftFactor d b δ₁ δ₂ r :=
  CanonicalLiteralProfileScalars.plainFactor_pos
    ((d.extract b).scale₁_pos false) ((d.extract b).scale₁_pos r) δ₁ δ₂

theorem rightFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < rightFactor d b δ₁ δ₂ r :=
  CanonicalLiteralProfileScalars.plainFactor_pos
    ((d.extract b).scale₂_pos false) ((d.extract b).scale₂_pos r) δ₁ δ₂

def balance (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralPlainBalance.ratio (leftFactor d b δ₁ δ₂ r) (rightFactor d b δ₁ δ₂ r)

theorem balance_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < balance d b δ₁ δ₂ r :=
  CanonicalLiteralPlainBalance.ratio_pos (leftFactor_pos d b δ₁ δ₂ r)
    (rightFactor_pos d b δ₁ δ₂ r)

def factor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  Real.sqrt (leftFactor d b δ₁ δ₂ r * rightFactor d b δ₁ δ₂ r)

theorem left_mul_balance (δ₁ δ₂ : ℝ) (r : Bool) :
    leftFactor d b δ₁ δ₂ r * balance d b δ₁ δ₂ r = factor d b δ₁ δ₂ r :=
  CanonicalLiteralPlainBalance.left_mul_ratio (leftFactor_pos d b δ₁ δ₂ r)
    (rightFactor_pos d b δ₁ δ₂ r)

theorem right_mul_balance_inv (δ₁ δ₂ : ℝ) (r : Bool) :
    rightFactor d b δ₁ δ₂ r * (balance d b δ₁ δ₂ r)⁻¹ = factor d b δ₁ δ₂ r :=
  CanonicalLiteralPlainBalance.right_mul_ratio_inv (leftFactor_pos d b δ₁ δ₂ r)
    (rightFactor_pos d b δ₁ δ₂ r)

/-- An active rectangle's actual ideal lower bounds give the lower
product window. This estimate then uses only the original annulus and
fixed tilt exponents. -/
theorem factor_le (δ₁ δ₂ hi : ℝ) (r : Bool) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false)
    (hlower : hi ^ (-2 : ℝ) ≤ (d.extract b).scale₁ false * (d.extract b).scale₂ false) :
    factor d b δ₁ δ₂ r ≤ Real.sqrt hi := by
  unfold factor leftFactor rightFactor
  rw [d.extracted_plainFactor_product b r δ₁ δ₂ hproduct]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (hi ^ (-2 : ℝ)) ^ (-1 / 2 + δ₁ + δ₂) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hhi) _)
        hlower (by linarith)
    _ = hi ^ ((-2 : ℝ) * (-1 / 2 + δ₁ + δ₂)) :=
      (Real.rpow_mul (zero_le_one.trans hhi) _ _).symm
    _ ≤ hi ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hhi (by linarith)
    _ = hi := Real.rpow_one _

theorem slotFactor_le_one (δ₁ δ₂ : ℝ) (j : Fin b.keep.card)
    (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ ≤ 1 := by
  let N := (d.extract b).base ^ (d.extract b).length j
  have hN : 0 < N := Real.rpow_pos_of_pos (zero_lt_one.trans (d.extract b).base_gt_one) _
  have hN₁ : 1 ≤ N := Real.one_le_rpow (d.extract b).base_gt_one.le
    ((d.extract b).length_pos j).le
  change Real.sqrt N * N ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ ≤ 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
  apply Real.rpow_le_one_of_one_le_of_nonpos hN₁
  unfold CanonicalLiteralProfileScalars.exponent
  linarith

theorem norm_inv_mul_self_le_one (c : ℂ) : ‖c⁻¹ * c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp only [hc, inv_zero, mul_zero, norm_zero, zero_le_one]
  · simp only [inv_mul_cancel₀ hc, norm_one, le_refl]

end CanonicalLiteralBalancedSchwartz

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)

def scale (c : ℂ) : (W.scale c).SchwartzModel window where
  left r := c • E.left r
  right := E.right
  slot := E.slot
  left_eq r u t y := by
    change (W.left r).profile u t y * c = c * E.left r y
    rw [E.left_eq]
    ring
  right_eq := E.right_eq
  slot_eq := E.slot_eq
  left_support r := (tsupport_smul_subset_right (fun _ : ℝ => c) (E.left r)).trans
    (E.left_support r)
  right_support := E.right_support
  slot_support := E.slot_support

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

local notation "outer" => d.commonScalar b *
  (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)
local notation "balance" => CanonicalLiteralBalancedSchwartz.balance d b δ₁ δ₂
local notation "factor" => CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂
local notation "transformed" => W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
  firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂

/-- The scalar-free balanced table is exactly `secondInput.scale
outer⁻¹` followed by the positive reciprocal plain balance. -/
def scalarFreeBalancedSecondInput (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) :
    ((transformed.scale outer⁻¹).balancePlain balance).SchwartzModel window := by
  apply (E.extract b).powerProfiles ((transformed.scale outer⁻¹).balancePlain balance)
    hcompact hpositive (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
    (fun r => (outer⁻¹ * outer) * (factor r : ℂ))
    (fun r => (factor r : ℂ))
    (fun j => (CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ))
  · intro r u t y hy
    change ((transformed.left r).profile u t y * outer⁻¹) * (balance r : ℂ) = _
    rw [W.secondInput_left_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u t hy]
    calc
      _ = (outer⁻¹ * outer) *
          ((CanonicalLiteralBalancedSchwartz.leftFactor d b δ₁ δ₂ r * balance r : ℝ) : ℂ) *
          ((W.left r).profile u t y *
            (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
        simp only [Complex.ofReal_mul, CanonicalLiteralBalancedSchwartz.leftFactor]
        ring
      _ = _ := by rw [CanonicalLiteralBalancedSchwartz.left_mul_balance] <;> rfl
  · intro r u t y hy
    change (transformed.right r).profile u t y * (balance r : ℂ)⁻¹ = _
    rw [W.secondInput_right_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u t hy]
    calc
      _ = ((CanonicalLiteralBalancedSchwartz.rightFactor d b δ₁ δ₂ r *
          (balance r)⁻¹ : ℝ) : ℂ) * ((W.right r).profile u t y *
            (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
        simp only [Complex.ofReal_mul, Complex.ofReal_inv, CanonicalLiteralBalancedSchwartz.rightFactor]
        ring
      _ = _ := by rw [CanonicalLiteralBalancedSchwartz.right_mul_balance_inv] <;> rfl
  · intro j t y hy
    exact W.secondInput_slot_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ j t hy

theorem scalarFreeBalanced_left_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).left r) ≤
      factor r * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  have hcoeff : ‖(outer⁻¹ * outer) * (factor r : ℂ)‖ ≤ factor r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (CanonicalLiteralBalancedSchwartz.norm_inv_mul_self_le_one outer) (Real.sqrt_nonneg _)
  exact (CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
    window hcompact hpositive ((outer⁻¹ * outer) * (factor r : ℂ))
      (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s (E.left r) (E.left_support r)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff
          (CanonicalLogProfiles.shapeCoefficient_nonneg window hcompact hpositive _ s))
        (apply_nonneg _ _))

theorem scalarFreeBalanced_right_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).right r) ≤
      factor r * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
      window hcompact hpositive (factor r : ℂ)
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s (E.right r) (E.right_support r)

theorem scalarFreeBalanced_slot_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (j : Fin b.keep.card) (s : Finset (ℕ × ℕ))
    (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j) ≤
      CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (E.slot (SlotRestriction.index b.keep j)) := by
  let L := CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).base ^ (d.extract b).length j)
    ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂
  have hL : 0 ≤ L := (CanonicalLiteralProfileScalars.plainFactor_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans (d.extract b).base_gt_one) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (d.extract b).base_gt_one) _) δ₁ δ₂).le
  have hL₁ : L ≤ 1 := CanonicalLiteralBalancedSchwartz.slotFactor_le_one d b δ₁ δ₂ j hδhi
  have hc : ‖(L : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL] using hL₁
  apply (CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
    window hcompact hpositive (L : ℂ) (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s
      (E.slot (SlotRestriction.index b.keep j))
      (E.slot_support (SlotRestriction.index b.keep j))).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc
      (CanonicalLogProfiles.shapeCoefficient_nonneg window hcompact hpositive _ s))
    (apply_nonneg _ _)

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralBalancedSchwartz.factor_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralBalancedSchwartz.slotFactor_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalancedSecondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_left_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_right_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_slot_bound
