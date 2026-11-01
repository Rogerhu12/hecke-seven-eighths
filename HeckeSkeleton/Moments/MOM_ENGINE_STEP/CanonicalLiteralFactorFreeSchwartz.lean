import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimeSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileFactorExtraction

/-!
# Actual Schwartz profiles after extracting every scale factor

The positive factor of every first-extracted occurrence is divided
out before the product is moved into the original first scalar.  The
redistributed table has exactly the same whole source.  Stripping its
combined scalar leaves the original test multiplied only by one fixed
real power of the profile variable.

The representatives below are constructed for this actual table.
Their finite-seminorm bounds do not contain any residual scale or
common/pool scalar.  They also exist for the zero scalar, where the
left test remains zero.  Subsequent extraction, atlas transport and
mask deletion use the existing representative transports.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)
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

local notation "oldScalar" => d.commonScalar b *
  (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)
local notation "combinedScalar" => oldScalar * (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)
local notation "transformed" => W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
  firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂
local notation "redistributed" => W.redistributedSecondInput (σ := σ) b P R
  power firstFixed poolFixed unitFixed firstElement poolElement unitElement
  hfirst hpool hunit δ₁ δ₂

/-- Each literal transformed profile is divided by its own positive
factor.  Only the combined original scalar is stripped, once. -/
def factorFreeSecondInput (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) :
    ((redistributed).scale combinedScalar⁻¹).SchwartzModel window := by
  apply (E.extract b).powerProfiles ((redistributed).scale combinedScalar⁻¹)
    hcompact hpositive (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
    (fun _ => combinedScalar⁻¹ * combinedScalar) (fun _ => 1) (fun _ => 1)
  · intro r u time y hy
    change ((((transformed).left r).profile u time y *
        (d.twoStageProfileLeftFactor b δ₁ δ₂ r : ℂ)⁻¹) *
        (d.twoStageProfileFactor b δ₁ δ₂ : ℂ)) * combinedScalar⁻¹ = _
    rw [W.secondInput_left_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u time hy]
    have hfactor : (d.twoStageProfileLeftFactor b δ₁ δ₂ r : ℂ) ≠ 0 := by
      exact_mod_cast (d.twoStageProfileLeftFactor_pos b δ₁ δ₂ r).ne'
    calc
      _ = ((d.twoStageProfileLeftFactor b δ₁ δ₂ r : ℂ) *
          (d.twoStageProfileLeftFactor b δ₁ δ₂ r : ℂ)⁻¹) *
        (combinedScalar⁻¹ * combinedScalar) *
        ((W.left r).profile u time y *
          (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
        unfold CanonicalLiteralRectangles.Atoms.twoStageProfileLeftFactor
        ring
      _ = _ := by rw [mul_inv_cancel₀ hfactor, one_mul] <;> rfl
  · intro r u time y hy
    change ((transformed).right r).profile u time y *
      (d.twoStageProfileRightFactor b δ₁ δ₂ r : ℂ)⁻¹ = _
    rw [W.secondInput_right_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u time hy]
    have hfactor : (d.twoStageProfileRightFactor b δ₁ δ₂ r : ℂ) ≠ 0 := by
      exact_mod_cast (d.twoStageProfileRightFactor_pos b δ₁ δ₂ r).ne'
    calc
      _ = ((d.twoStageProfileRightFactor b δ₁ δ₂ r : ℂ) *
          (d.twoStageProfileRightFactor b δ₁ δ₂ r : ℂ)⁻¹) *
        ((W.right r).profile u time y *
          (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
        unfold CanonicalLiteralRectangles.Atoms.twoStageProfileRightFactor
        ring
      _ = _ := by rw [mul_inv_cancel₀ hfactor] <;> rfl
  · intro j time y hy
    change ((transformed).slot j).profile time y *
      (d.twoStageProfileSlotFactor b δ₁ δ₂ j : ℂ)⁻¹ = _
    rw [W.secondInput_slot_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ j time hy]
    have hfactor : (d.twoStageProfileSlotFactor b δ₁ δ₂ j : ℂ) ≠ 0 := by
      exact_mod_cast (d.twoStageProfileSlotFactor_pos b δ₁ δ₂ j).ne'
    calc
      _ = ((d.twoStageProfileSlotFactor b δ₁ δ₂ j : ℂ) *
          (d.twoStageProfileSlotFactor b δ₁ δ₂ j : ℂ)⁻¹) *
        ((W.slot (SlotRestriction.index b.keep j)).profile time y *
          (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
        unfold CanonicalLiteralRectangles.Atoms.twoStageProfileSlotFactor
        ring
      _ = _ := by rw [mul_inv_cancel₀ hfactor] <;> rfl

theorem factorFree_left_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.factorFreeSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).left r) ≤
      CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  apply (CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
    window hcompact hpositive (combinedScalar⁻¹ * combinedScalar)
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s (E.left r) (E.left_support r)).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (CanonicalLiteralBalancedSchwartz.norm_inv_mul_self_le_one combinedScalar)
      (CanonicalLogProfiles.shapeCoefficient_nonneg window hcompact hpositive _ s))
    (apply_nonneg _ _)

theorem factorFree_right_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.factorFreeSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).right r) ≤
      CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  simpa only [norm_one, one_mul] using
    CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound window hcompact hpositive
      1 (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s (E.right r) (E.right_support r)

theorem factorFree_slot_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (j : Fin b.keep.card) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.factorFreeSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j) ≤
      CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (E.slot (SlotRestriction.index b.keep j)) := by
  simpa only [norm_one, one_mul] using
    CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound window hcompact hpositive
      1 (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s
      (E.slot (SlotRestriction.index b.keep j))
      (E.slot_support (SlotRestriction.index b.keep j))

theorem factorFreeSecondInput_prime_support (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) {target : Set ℝ}
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support
      ((E.factorFreeSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j)
      ⊆ target := by
  intro j
  exact (CanonicalLiteralSchwartzProfiles.powerSchwartz_support_subset
    window hcompact hpositive 1 _ (E.slot (SlotRestriction.index b.keep j))
    (E.slot_support (SlotRestriction.index b.keep j))).trans
      (hprime (SlotRestriction.index b.keep j))

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.factorFreeSecondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.factorFree_left_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.factorFree_right_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.factorFree_slot_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.factorFreeSecondInput_prime_support
