import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices

set_option linter.unusedSectionVars false

/-!
# Original numerical windows for the fixed engine choices

The original domain supplies the comparison scales before the first
Cartesian source is constructed. Both plain exponents are the same
fixed original box exponent. The annulus and cutoff windows use the
already chosen full threshold, independently of all moving profiles.

The column exponent below is the input to
`CompleteMovingRowRecipe.literalPrimitiveFirstSource_column_norm`.
That theorem uses the original recipe and its `fullSupportParameters`;
no change to the original remaining mask is made here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CanonicalOriginalParentFactory CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

@[simp] theorem first_plainBound (b : Box) : b.firstBox.plainBound = b.lengthBound := rfl

@[simp] theorem first_columnBound (b : Box) : b.firstBox.columnBound = b.columnBound := rfl

variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}

/-- The domain transported to the comparison scales used by the
actual source, with all original parameters retained. -/
abbrev comparison_domain
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) :
    PairedEngineDomain centered d a Z
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
      floor padding := domain.canonicalComparisonScales

theorem slot_total_nonneg
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) : 0 ≤ a.z := by
  sorry

theorem total_nonneg
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) :
    0 ≤ a.n₁ + a.n₂ + a.z := by
  sorry

theorem total_le (b : Box)
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax) :
    a.n₁ + a.n₂ + a.z ≤ b.lengthBound := by
  sorry

theorem total_geometry_le (b : Box)
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax) :
    a.n₁ + a.n₂ + d.geometry.totalLength ≤ b.lengthBound := by
  sorry

/-- The eight original windows consumed by the first source and the
raw analytic-input factories. The two exponents are both
`b.lengthBound`, definitionally `b.firstBox.plainBound`. -/
theorem scale_windows (b : Box)
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax) :
    0 < comparisonScale centered Z a.n₁ Y₁ ∧
    0 < comparisonScale centered Z a.n₂ Y₂ ∧
    Z ^ a.n₁ ≤ Z ^ b.lengthBound ∧
    Z ^ a.n₂ ≤ Z ^ b.lengthBound ∧
    comparisonScale centered Z a.n₁ Y₁ ≤ Z ^ b.lengthBound ∧
    comparisonScale centered Z a.n₂ Y₂ ≤ Z ^ b.lengthBound ∧
    a.n₁ + a.n₂ + a.z ≤ b.lengthBound ∧
    b.lengthBound + b.lengthBound + d.geometry.totalLength + b.loss ≤ b.columnBound := by
  sorry

/-- The complete raw character norm box includes the second common
root and the actual cutoff allowance. -/
theorem raw_width_le (b : Box) (a : RealParameters)
    (hwidth : a.m + a.q ≤ b.widthMax) :
    a.m + a.q + b.columnBound + (2 * b.loss + b.loss) ≤ b.rawNormBound := by
  sorry

/-- Only fixed numerical windows are stored here. In particular no
source, profile, column, terminal or family estimate is an input. -/
structure FixedWindows (b : Box) (Z : ℝ) : Prop where
  scale : 1 < Z
  first_large : b.firstBox.threshold ≤ Z
  allocation_large : OriginalPairAllowanceProduction.annulusThreshold b.hi b.error ≤ Z
  upper_annulus : b.hi ^ (b.cap + 2) ≤ Z ^ b.loss
  lower_annulus : (b.lo ^ (b.cap + 2))⁻¹ ≤ Z ^ b.loss
  slot_annulus : b.hi ^ b.cap ≤ Z ^ b.error
  double_slot_annulus : b.hi ^ (2 * b.cap) ≤ Z ^ b.error
  single_annulus : b.hi ≤ Z ^ (2 * b.loss)
  first_cutoff_lower : 1 ≤ b.firstBox.cutoff Z
  first_cutoff_upper : b.firstBox.cutoff Z ≤ Z ^ b.loss
  second_cutoff_lower : 1 ≤ b.secondCutoff Z
  second_cutoff_upper : b.secondCutoff Z ≤ Z ^ b.loss
  pool_large : 2 * (b.rowBound / ((b.step / 3) / 2) +
    b.columnBound / ((b.step / 3) / 2)) ≤ Z ^ (b.step / 3 - b.loss)

/-- Every large-scale premise follows from the single fixed threshold
chosen before the original data and profiles. -/
theorem fixed_windows (b : Box) {Z : ℝ} (hlarge : b.fullThreshold ≤ Z) :
    FixedWindows b Z := by
  sorry

theorem tilt_sum_le_half (b : Box) : b.tilt + b.tilt ≤ 1 / 2 := by
  sorry

/-- The same small parameters satisfy the allocation margin, moving
width decrease and both prime-pool separations. -/
theorem small_parameters (b : Box) :
    0 < b.loss ∧ 0 < b.error ∧ 0 < b.tilt ∧ b.tilt + b.tilt ≤ 1 / 2 ∧
    2 * b.loss + b.loss ≤ b.error ∧
    2 * (2 * b.loss + b.loss) ≤ b.step ∧
    b.loss < b.step / 6 ∧ b.loss < b.step / 3 := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.scale_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.fixed_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.raw_width_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.small_parameters
