import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSchwartzProfiles

set_option linter.unusedSectionVars false

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

theorem leftFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < leftFactor d b δ₁ δ₂ r := by
  sorry

theorem rightFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < rightFactor d b δ₁ δ₂ r := by
  sorry

def balance (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralPlainBalance.ratio (leftFactor d b δ₁ δ₂ r) (rightFactor d b δ₁ δ₂ r)

theorem balance_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < balance d b δ₁ δ₂ r := by
  sorry

def factor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  Real.sqrt (leftFactor d b δ₁ δ₂ r * rightFactor d b δ₁ δ₂ r)

theorem left_mul_balance (δ₁ δ₂ : ℝ) (r : Bool) :
    leftFactor d b δ₁ δ₂ r * balance d b δ₁ δ₂ r = factor d b δ₁ δ₂ r := by
  sorry

theorem right_mul_balance_inv (δ₁ δ₂ : ℝ) (r : Bool) :
    rightFactor d b δ₁ δ₂ r * (balance d b δ₁ δ₂ r)⁻¹ = factor d b δ₁ δ₂ r := by
  sorry

/-- An active rectangle's actual ideal lower bounds give the lower
product window. This estimate then uses only the original annulus and
fixed tilt exponents. -/
theorem factor_le (δ₁ δ₂ hi : ℝ) (r : Bool) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false)
    (hlower : hi ^ (-2 : ℝ) ≤ (d.extract b).scale₁ false * (d.extract b).scale₂ false) :
    factor d b δ₁ δ₂ r ≤ Real.sqrt hi := by
  sorry

theorem slotFactor_le_one (δ₁ δ₂ : ℝ) (j : Fin b.keep.card)
    (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ ≤ 1 := by
  sorry

theorem norm_inv_mul_self_le_one (c : ℂ) : ‖c⁻¹ * c‖ ≤ 1 := by
  sorry

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
    (((transformed).scale outer⁻¹).balancePlain balance).SchwartzModel window := by
  apply (E.extract b).powerProfiles (((transformed).scale outer⁻¹).balancePlain balance)
    hcompact hpositive (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
    (fun r => (outer⁻¹ * outer) * (factor r : ℂ))
    (fun r => (factor r : ℂ))
    (fun j => (CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ))
  · intro r u t y hy
    change (((transformed).left r).profile u t y * outer⁻¹) * (balance r : ℂ) = _
    rw [W.secondInput_left_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u t hy]
    calc
      _ = (outer⁻¹ * outer) *
          ((CanonicalLiteralBalancedSchwartz.leftFactor d b δ₁ δ₂ r * balance r : ℝ) : ℂ) *
          ((W.left r).profile u t y *
            ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
        simp only [Complex.ofReal_mul, CanonicalLiteralBalancedSchwartz.leftFactor]
        ring
      _ = _ := by rw [CanonicalLiteralBalancedSchwartz.left_mul_balance] <;> rfl
  · intro r u t y hy
    change ((transformed).right r).profile u t y * (balance r : ℂ)⁻¹ = _
    rw [W.secondInput_right_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u t hy]
    calc
      _ = ((CanonicalLiteralBalancedSchwartz.rightFactor d b δ₁ δ₂ r *
          (balance r)⁻¹ : ℝ) : ℂ) * ((W.right r).profile u t y *
            ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
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
  sorry

theorem scalarFreeBalanced_right_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).right r) ≤
      factor r * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  sorry

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
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralBalancedSchwartz.factor_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralBalancedSchwartz.slotFactor_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalancedSecondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_left_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_right_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_slot_bound
