module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalSupport

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform original windows for the V2 tails

The frame fixes the annulus and its threshold. Original profile
seminorms bound each whole centered coefficient. Nonzero coefficients
supply the active whole-ideal window and its injective tuple count.
The genuine joint row budget also puts the working row exponent in
[0,2], so both directions of the first physical radius are controlled.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

/-- Only this point-evaluation order of the original profiles is used. -/
def originalOrders : Finset (ℕ × ℕ) := {(0, 0)}

/-- The upper end of every allowed original annulus in this frame. -/
def originalAnnulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (2 * (frame.upper * (2 : ℝ) ^ (6 * (widthBand (recipeInductionSigma c) 2 + 1))))

def originalThreshold (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  originalAnnulus c frame ^ (c.geometry.slots + 2)

def originalColumnExponent (c : TargetContext K) : ℝ :=
  3 + recipeInductionSigma c / 16

theorem originalAnnulus_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ originalAnnulus c frame := le_max_left _ _

theorem originalThreshold_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ originalThreshold c frame :=
  one_le_pow₀ (originalAnnulus_one_le c frame)

theorem originalColumnExponent_nonneg (c : TargetContext K) :
    0 ≤ originalColumnExponent c := by
  have hs := (recipeInduction_budget (c := c)).1
  dsimp [originalColumnExponent]
  positivity

variable {c : TargetContext K} (call : Call c)

theorem original_window_upper (input : ProfileInput call) :
    call.window ⊆ Set.Iic (originalAnnulus c call.frame) := by
  intro x hx
  have hu : call.prepared.upper ≤
      call.frame.upper * (2 : ℝ) ^ call.rankBound := by
    rw [input.regular.upper]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
        (Nat.sub_le call.rankBound call.rank))
      (by linarith [call.frame.upper_large])
  apply hx.2.trans
  exact (mul_le_mul_of_nonneg_left hu (by norm_num)).trans (le_max_right _ _)

theorem working_total_nonneg :
    0 ≤ call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.localizedData.geometry.totalLength := by
  exact add_nonneg
    (add_nonneg call.domain.plain_left_nonneg call.domain.plain_right_nonneg)
    (Finset.sum_nonneg (fun i _ =>
      (call.localizedData.geometry.slots i).length_pos.le))

theorem working_total_le :
    call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.localizedData.geometry.totalLength ≤ 2 + recipeInductionSigma c / 16 := by
  change call.node.parameters.n₁ + call.node.parameters.n₂ +
    call.node.data.geometry.totalLength ≤ _
  rw [← call.domain.total_length]
  linarith [call.domain.padded_core, call.width_le]

theorem working_slots_le : call.localizedData.geometry.slotCount ≤ c.geometry.slots :=
  call.slots_le

theorem working_comparison_product :
    call.base ^ call.workingComparison₁ * call.base ^ call.workingComparison₂ =
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂) := by
  rw [← Real.rpow_add call.base_pos]
  congr 1
  cases hcentered : call.node.centered with
  | false => simp [Call.workingComparison₁, Call.workingComparison₂,
      hcentered, Call.workingParameters]
  | true => simpa [Call.workingComparison₁, Call.workingComparison₂,
      hcentered, Call.workingParameters] using call.node.comparison_sum

theorem supportLength_nonneg : 0 ≤ call.supportLength := by
  have hN : 1 ≤ (Arithmetic.data c).exteriorNorm call.oldSupport := by
    change (1 : ℝ) ≤ (Ideal.absNorm call.oldSupport.val : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (fun h => call.oldSupport.property.1 (Ideal.absNorm_eq_zero_iff.mp h)))
  exact div_nonneg (Real.log_nonneg hN) (Real.log_pos call.domain.scale).le

/-- A real original row pays the complete effective deletion support. -/
theorem support_norm_le_width (hactive : call.Active) :
    (Arithmetic.data c).exteriorNorm call.oldSupport ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
  obtain ⟨u, hu⟩ := hactive
  have hbudget := call.source.pairedJointBudget u hu
  have hN := call.localizedSource.source.recipe.moving.effectiveFullSupport_norm_le
    call.localizedSource.source.recipe.remaining
  have hrow : 1 ≤ idealNorm K u := one_le_idealNorm K u
  calc
    _ ≤ idealNorm K (call.localizedSource.source.recipe.moving.fullMaskSupport
        call.localizedSource.source.recipe.remaining) := hN
    _ ≤ idealNorm K u *
        idealNorm K (call.localizedSource.source.recipe.moving.fullMaskSupport
          call.localizedSource.source.recipe.remaining) :=
      le_mul_of_one_le_left (idealNorm_pos K _).le hrow
    _ ≤ _ := hbudget

theorem supportLength_le_width (hactive : call.Active) :
    call.supportLength ≤ call.node.parameters.m + call.node.parameters.q := by
  have hlog := Real.log_le_log
    ((Arithmetic.data c).exteriorNorm_pos call.oldSupport)
    (support_norm_le_width call hactive)
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

theorem working_m_nonneg (hactive : call.Active) : 0 ≤ call.workingParameters.m := by
  change 0 ≤ call.node.parameters.m + call.node.parameters.q - call.supportLength
  exact sub_nonneg.mpr (supportLength_le_width call hactive)

theorem working_m_le : call.workingParameters.m ≤ 2 := by
  change call.node.parameters.m + call.node.parameters.q - call.supportLength ≤ 2
  linarith [call.width_le, supportLength_nonneg call]

/-- No estimate on the whole coefficient is an input: arithmetic and
the one original point-evaluation seminorm prove it. -/
theorem original_coefficient_norm_le (input : ProfileInput call)
    (horders : originalOrders ⊆ input.orders)
    (i : call.workingRaw.Column) (hi : i ∈ call.workingRaw.exteriorColumns) :
    ‖call.workingValues.coefficient call.node.centered i‖ ≤
      2 * input.amplitude ^ (c.geometry.slots + 2) := by
  have hzero : (0, 0) ∈ input.orders :=
    horders (by simp only [originalOrders, Finset.mem_singleton])
  have h := ScalarAtoms.tailsV2_coefficient_norm_le_raw_profile_window
    call.workingAtoms input.localized
    (MovingArithmetic.tailsV2_arithmeticAtoms_left_norm_le_one
      call.localizedSource.source.recipe PUnit.unit)
    (MovingArithmetic.tailsV2_arithmeticAtoms_right_norm_le_one
      call.localizedSource.source.recipe PUnit.unit)
    (MovingArithmetic.tailsV2_arithmeticAtoms_prime_norm_le_one
      call.localizedSource.source.recipe PUnit.unit)
    c.geometry.slots (working_slots_le call) input.amplitude_one_le call.base_pos hzero
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    call.node.centered (fun _ => (Real.rpow_pos_of_pos call.base_pos _).le)
    (fun _ => working_comparison_product call) i (Finset.mem_filter.mp hi).1
  have hp : call.base ^
      (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.localizedData.geometry.totalLength) / 2) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        (show -(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.localizedData.geometry.totalLength) / 2 ≤ 0 by
          linarith [working_total_nonneg call])
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _)))

/-- Nonzero whole coefficients use a single genuine nonzero rectangle;
the Cartesian union may retain arbitrarily many harmless zero columns. -/
theorem original_active_ideal_norm_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : call.workingRaw.Column) (hi : i ∈ call.workingRaw.exteriorColumns)
    (hci : call.workingValues.coefficient call.node.centered i ≠ 0) :
    (Ideal.absNorm (call.workingRaw.columnExterior i).val : ℝ) ≤
      call.base ^ originalColumnExponent c := by
  have h := ScalarAtoms.tailsV2_original_active_column_norm_le_annulus
    call.workingAtoms input.localized (originalAnnulus c call.frame)
    (zero_le_one.trans (originalAnnulus_one_le c call.frame)) call.base_pos
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    (original_window_upper call input) call.node.centered
    (fun _ => (Real.rpow_pos_of_pos call.base_pos _).le)
    (fun _ => working_comparison_product call) i hi hci
  have hconstant : originalAnnulus c call.frame ^
      (call.localizedData.geometry.slotCount + 2) ≤ originalThreshold c call.frame :=
    pow_le_pow_right₀ (originalAnnulus_one_le c call.frame)
      (Nat.add_le_add_right (working_slots_le call) 2)
  have hpower := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
    (working_total_le call)
  calc
    _ ≤ originalAnnulus c call.frame ^ (call.localizedData.geometry.slotCount + 2) *
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.localizedData.geometry.totalLength) := h
    _ ≤ originalThreshold c call.frame *
        call.base ^ (2 + recipeInductionSigma c / 16) :=
      mul_le_mul hconstant hpower (Real.rpow_nonneg call.base_pos.le _)
        (zero_le_one.trans (originalThreshold_one_le c call.frame))
    _ ≤ call.base * call.base ^ (2 + recipeInductionSigma c / 16) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg call.base_pos.le _)
    _ = call.base ^ originalColumnExponent c := by
      rw [show originalColumnExponent c = 1 + (2 + recipeInductionSigma c / 16) by
        dsimp [originalColumnExponent]; ring]
      simpa only [Real.rpow_one] using
        (Real.rpow_add call.base_pos (1 : ℝ) (2 + recipeInductionSigma c / 16)).symm

def activeOriginalColumns : Finset call.workingRaw.Column :=
  call.workingRaw.exteriorColumns.filter
    (fun i => call.workingValues.coefficient call.node.centered i ≠ 0)

/-- The factors are the two original ideals and every original prime
occurrence, padded by units up to the fixed slot cap. -/
theorem activeOriginalColumns_card (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) :
    ((activeOriginalColumns call).card : ℝ) ≤
      (idealCountConstant K * call.base ^ originalColumnExponent c) ^
        (c.geometry.slots + 2) := by
  apply whole_ideal_tuple_card (activeOriginalColumns call)
    (call.workingRaw.paddedOriginalIdealFactors c.geometry.slots (working_slots_le call))
    (call.workingRaw.paddedOriginalIdealFactors_injective c.geometry.slots
      (working_slots_le call)).injOn
    (call.base ^ originalColumnExponent c)
    (Real.one_le_rpow call.domain.scale.le (originalColumnExponent_nonneg c))
  · intro i hi
    rw [call.workingRaw.paddedOriginalIdealFactors_product]
    exact call.workingRaw.columnIdeal_ne_zero i
  · intro i hi
    have him := Finset.mem_filter.mp hi
    rw [call.workingRaw.paddedOriginalIdealFactors_product,
      ← call.workingRaw.columnExterior_val_of_mem i him.1]
    exact original_active_ideal_norm_le call input hlarge i him.1 him.2

variable {call} {p : SourceParameters c}
variable (F : FirstPresentation call p) (hF : F.Realizes)

include hF

theorem first_index_mem (i : F.source.Column) (hi : i ∈ F.source.columns) :
    F.index i ∈ call.workingRaw.exteriorColumns := by
  rw [← hF.columns]
  exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

theorem first_coefficient_norm_le (input : ProfileInput call)
    (horders : originalOrders ⊆ input.orders)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    ‖F.coefficient i‖ ≤ 2 * input.amplitude ^ (c.geometry.slots + 2) :=
  original_coefficient_norm_le call input horders (F.index i) (first_index_mem F hF i hi)

theorem first_active_ideal_norm_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : F.source.Column) (hi : i ∈ F.source.columns) (hci : F.coefficient i ≠ 0) :
    (Ideal.absNorm (F.source.ideal i).val : ℝ) ≤ call.base ^ originalColumnExponent c := by
  rw [hF.ideal]
  exact original_active_ideal_norm_le call input hlarge
    (F.index i) (first_index_mem F hF i hi) hci

theorem first_inverse_radius_le :
    F.source.radius.val⁻¹ ≤ call.base ^ (2 : ℝ) := by
  rw [hF.radius, Real.rpow_neg call.base_pos.le, inv_inv]
  exact Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (working_m_le call)

theorem first_radius_le_one : F.source.radius.val ≤ 1 := by
  rw [hF.radius]
  simpa only [Real.rpow_zero] using
    Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
      (neg_nonpos.mpr (working_m_nonneg call hF.active))

theorem first_profile_nonzero_coefficients (i j : F.source.Column)
    (hprofile : F.source.profiles i j ≠ 0) :
    F.coefficient i ≠ 0 ∧ F.coefficient j ≠ 0 := by
  rw [hF.profile] at hprofile
  constructor
  · intro hi
    exact hprofile (by simp only [FirstPresentation.originalProfile, hi, zero_mul, zero_smul])
  · intro hj
    exact hprofile (by
      simp only [FirstPresentation.originalProfile, hj, star_zero, mul_zero, zero_smul])

theorem first_mask_norm_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) (i : F.source.Column)
    (hi : i ∈ (F.source.source v).leftColumns) (hci : F.coefficient i ≠ 0) :
    (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        ((F.source.source v).mask))).val ≤ call.base ^ originalColumnExponent c := by
  change (sIntegerElementNorm K _
    (sIntegerMaskGenerator K _ ((F.source.block v).mask F.source.mask))).val ≤ _
  rw [hF.mask]
  exact (PhysicalBlock.tailsV2_principal_mask_norm_le_original_column
    (F.source.block v) (Arithmetic.context c) F.source.columns i hi).trans
      (first_active_ideal_norm_le F hF input hlarge i (Finset.mem_filter.mp hi).1 hci)

theorem first_modulus_norm_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) (i : F.source.Column)
    (hi : i ∈ (F.source.source v).leftColumns) (j : F.source.Column)
    (hj : j ∈ (F.source.source v).rightColumns)
    (hci : F.coefficient i ≠ 0) (hcj : F.coefficient j ≠ 0) :
    (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨((F.source.source v).pairs i j).modulus,
        ((F.source.source v).pairs i j).modulus_ne_zero⟩).val ≤
      call.base ^ (2 * originalColumnExponent c) := by
  have hmod := PhysicalBlock.tailsV2_first_modulus_norm_le_original_product
    (F.source.block v) (Arithmetic.units_are_sixth c) (Arithmetic.context c)
    F.source.columns F.source.columns F.source.profiles i hi j hj
  have hleft := first_active_ideal_norm_le F hF input hlarge i
    (Finset.mem_filter.mp hi).1 hci
  have hright := first_active_ideal_norm_le F hF input hlarge j
    (Finset.mem_filter.mp hj).1 hcj
  apply hmod.trans
  rw [map_mul, Nat.cast_mul]
  exact (mul_le_mul hleft hright (Nat.cast_nonneg _)
    (Real.rpow_nonneg call.base_pos.le _)).trans_eq (by
      rw [← Real.rpow_add call.base_pos]
      congr 1
      ring)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.original_coefficient_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.original_active_ideal_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.activeOriginalColumns_card
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.working_m_nonneg
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_modulus_norm_le

