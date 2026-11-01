import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices

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
  rw [domain.total_length]
  exact Finset.sum_nonneg fun i _ => (d.geometry.slots i).length_pos.le

theorem total_nonneg
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) :
    0 ≤ a.n₁ + a.n₂ + a.z :=
  add_nonneg (add_nonneg domain.plain_left_nonneg domain.plain_right_nonneg)
    (slot_total_nonneg domain)

theorem total_le (b : Box)
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax) :
    a.n₁ + a.n₂ + a.z ≤ b.lengthBound := by
  change a.n₁ + a.n₂ + a.z ≤ b.widthMax + b.paddingMax
  linarith [domain.padded_core]

theorem total_geometry_le (b : Box)
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax) :
    a.n₁ + a.n₂ + d.geometry.totalLength ≤ b.lengthBound := by
  simpa only [domain.total_length] using total_le b domain hwidth hpadding

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
  obtain ⟨hY₁, hY₂, hn₁, hn₂, hY₁le, hY₂le, hcolumn, _⟩ :=
    original_scale_windows b.firstBox domain hwidth hpadding
  exact ⟨hY₁, hY₂,
    Real.rpow_le_rpow_of_exponent_le domain.scale.le hn₁,
    Real.rpow_le_rpow_of_exponent_le domain.scale.le hn₂,
    hY₁le, hY₂le, total_le b domain hwidth hpadding, hcolumn⟩

/-- The complete raw character norm box includes the second common
root and the actual cutoff allowance. -/
theorem raw_width_le (b : Box) (a : RealParameters)
    (hwidth : a.m + a.q ≤ b.widthMax) :
    a.m + a.q + b.columnBound + (2 * b.loss + b.loss) ≤ b.rawNormBound := by
  unfold Box.rawNormBound
  linarith

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
  have hZ : 1 < Z := b.fullThreshold_spec.1.trans_le hlarge
  have hfirst : b.firstBox.threshold ≤ Z :=
    b.fullThreshold_spec.2.2.1.trans hlarge
  have hallowance : OriginalPairAllowanceProduction.annulusThreshold b.hi b.error ≤ Z :=
    b.fullThreshold_spec.2.2.2.1.trans hlarge
  have hthreshold : b.threshold ≤ Z := b.fullThreshold_spec.2.1.trans hlarge
  have hannulus := b.threshold_windows Z hthreshold
  have hslots := b.fullThreshold_spec.2.2.2.2 Z hlarge
  exact {
    scale := hZ
    first_large := hfirst
    allocation_large := hallowance
    upper_annulus := hannulus.1
    lower_annulus := hannulus.2.1
    slot_annulus := (pow_le_pow_right₀ b.hi_ge_one
      (show b.cap ≤ 2 * b.cap by omega)).trans hslots.1
    double_slot_annulus := hslots.1
    single_annulus := hslots.2
    first_cutoff_lower := b.firstBox.cutoff_ge_one hZ.le
    first_cutoff_upper := b.firstCutoff_le Z hZ.le
    second_cutoff_lower := b.secondCutoff_ge_one Z hZ.le
    second_cutoff_upper := b.secondCutoff_le Z hZ.le
    pool_large := hannulus.2.2 }

theorem tilt_sum_le_half (b : Box) : b.tilt + b.tilt ≤ 1 / 2 := by
  linarith [b.tilt_le_quarter]

/-- The same small parameters satisfy the allocation margin, moving
width decrease and both prime-pool separations. -/
theorem small_parameters (b : Box) :
    0 < b.loss ∧ 0 < b.error ∧ 0 < b.tilt ∧ b.tilt + b.tilt ≤ 1 / 2 ∧
    2 * b.loss + b.loss ≤ b.error ∧
    2 * (2 * b.loss + b.loss) ≤ b.step ∧
    b.loss < b.step / 6 ∧ b.loss < b.step / 3 :=
  ⟨b.loss_pos, b.error_pos, b.tilt_pos, tilt_sum_le_half b,
    b.support_error_le, b.width_margin, b.pool_separation.1, b.pool_separation.2⟩

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.scale_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.fixed_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.raw_width_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineOriginalWindows.small_parameters
