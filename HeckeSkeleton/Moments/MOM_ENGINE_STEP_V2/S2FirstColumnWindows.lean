import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2OriginalColumnWindow
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstFamilyData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform original column windows for S2

One annulus covers every rank of the fixed clipping schedule. A single
scale threshold absorbs its fixed power before the moving call or its
profiles are chosen. The actual common ideal is then divided out.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

universe u v w

private theorem field_eq_of_heq {Index : Sort u} {Data : Index → Sort v} {Value : Sort w}
    (field : ∀ i, Data i → Value) {i j : Index} (hij : i = j)
    {x : Data i} {y : Data j} (hxy : HEq x y) : field i x = field j y := by
  subst j
  cases hxy
  rfl

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

def frameRange (c : TargetContext K) (frame : SourceFrame) : StrictProfileRange :=
  (StrictProfileRange.ofSchedule frame.lower frame.upper frame.lower_pos frame.interval.le
    (6 * (widthBand (recipeInductionSigma c) 2 + 1))).expanded

def columnAnnulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (max (frameRange c frame).upper (1 / (frameRange c frame).lower))

theorem columnAnnulus_one (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ columnAnnulus c frame := le_max_left _ _

theorem frameRange_subset (c : TargetContext K) (frame : SourceFrame) :
    Set.Icc (frameRange c frame).lower (frameRange c frame).upper ⊆
      Set.Icc (columnAnnulus c frame)⁻¹ (columnAnnulus c frame) := by
  have hA : 0 < columnAnnulus c frame := zero_lt_one.trans_le (columnAnnulus_one c frame)
  have hlow : (columnAnnulus c frame)⁻¹ ≤ (frameRange c frame).lower := by
    rw [← one_div]
    apply (div_le_iff₀ hA).mpr
    have hi : 1 / (frameRange c frame).lower ≤ columnAnnulus c frame :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hm := (div_le_iff₀ (frameRange c frame).lower_pos).mp hi
    simpa only [mul_comm] using hm
  intro x hx
  exact ⟨hlow.trans hx.1, hx.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩

def columnDemand (c : TargetContext K) (p : SourceParameters c) (frame : SourceFrame) :
    UniformDemand where
  orders := ∅
  threshold := Classical.choose
    (annulus_power_threshold c.geometry.slots (columnAnnulus c frame) p.loss p.loss_pos)
  threshold_one_le := (Classical.choose_spec
    (annulus_power_threshold c.geometry.slots (columnAnnulus c frame) p.loss p.loss_pos)).1.le

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c} {frame : SourceFrame}

theorem call_window_subset (input : ProfileInput call) (hframe : call.frame = frame) :
    call.window ⊆ Set.Icc (columnAnnulus c frame)⁻¹ (columnAnnulus c frame) := by
  apply Set.Subset.trans _ (frameRange_subset c frame)
  subst frame
  rw [Call.window, input.regular.lower, input.regular.upper]
  exact StrictProfileRange.expanded_contains_schedule call.frame.lower call.frame.upper
    call.frame.lower_pos call.frame.interval.le call.rankBound call.rank

theorem columnDemand_power (input : ProfileInput call)
    (ready : (columnDemand c p frame).Ready call input) :
    (columnAnnulus c frame) ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss :=
  (Classical.choose_spec
    (annulus_power_threshold c.geometry.slots (columnAnnulus c frame) p.loss p.loss_pos)).2
      call.base ready.large

theorem source_full_column_window (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (columnDemand c p frame).Ready call input)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) (hcoeff : F.coefficient i ≠ 0) :
    call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z - p.loss) ≤ (Arithmetic.data c).exteriorNorm (F.source.ideal i) ∧
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + p.loss) := by
  have hm : F.index i ∈ call.workingRaw.exteriorColumns := by
    rw [← hF.columns]
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  let annulus := columnAnnulus c frame
  have hannulus : 1 ≤ annulus := columnAnnulus_one c frame
  have hannulus_pos : 0 < annulus := zero_lt_one.trans_le hannulus
  have hw := original_column_norm_bounds
    (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
    (Y₁ := call.base ^ call.workingComparison₁) (Y₂ := call.base ^ call.workingComparison₂)
    call.workingAtoms input.localized
    annulus⁻¹ annulus (inv_nonneg.mpr hannulus_pos.le) hannulus_pos.le call.base_pos
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _) (call_window_subset input hframe)
    call.node.centered (fun _ => (Real.rpow_pos_of_pos call.base_pos _).le)
    (by
      intro hcentered
      simpa only [Call.workingComparison₁, Call.workingComparison₂, hcentered, if_true]
        using call.domain.comparison_product_eq_power hcentered)
    (F.index i) hm hcoeff
  have hcap : call.localizedData.geometry.slotCount ≤ c.geometry.slots := call.slots_le
  have hpower : annulus ^ (call.localizedData.geometry.slotCount + 2) ≤ call.base ^ p.loss :=
    (pow_le_pow_right₀ hannulus (Nat.add_le_add_right hcap 2)).trans
      (columnDemand_power input ready)
  have hnpos : 0 < annulus ^ (call.localizedData.geometry.slotCount + 2) :=
    pow_pos hannulus_pos _
  have hlength : call.localizedData.geometry.totalLength = call.workingParameters.z :=
    call.domain.total_length
  rw [hlength] at hw
  rw [hF.ideal i]
  constructor
  · calc
      _ = call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) / call.base ^ p.loss := Real.rpow_sub call.base_pos _ _
      _ ≤ call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) /
          annulus ^ (call.localizedData.geometry.slotCount + 2) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg call.base_pos.le _) hnpos hpower
      _ = annulus⁻¹ ^ (call.localizedData.geometry.slotCount + 2) *
          call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
            call.workingParameters.z) := by rw [inv_pow]; ring
      _ ≤ _ := hw.1
  · calc
      _ ≤ annulus ^ (call.localizedData.geometry.slotCount + 2) *
          call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
            call.workingParameters.z) := hw.2
      _ ≤ call.base ^ p.loss * call.base ^
          (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z) :=
        mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg call.base_pos.le _)
      _ = _ := by rw [← Real.rpow_add call.base_pos]; congr 1; ring

theorem chart_left_coefficient (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (i : F.source.Column) :
    (F.source.charts v D).leftCoefficient i = F.coefficient i *
      ((((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) : ℂ)) := by
  have hfield := field_eq_of_heq
    (fun (profiles : F.source.Column → F.source.Column →
        SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      (chart : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
        (Arithmetic.localMeasures (K := K)) (F.source.block v) (Arithmetic.context c)
        F.source.columns F.source.columns profiles
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val) =>
      chart.leftCoefficient i) hF.profile (hF.chart v D)
  rw [hfield]
  rfl

theorem chart_right_coefficient (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset)
    (i : F.source.Column) :
    (F.source.charts v D).rightCoefficient i = F.coefficient i *
      ((((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) : ℂ)) := by
  have hfield := field_eq_of_heq
    (fun (profiles : F.source.Column → F.source.Column →
        SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      (chart : FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
        (Arithmetic.localMeasures (K := K)) (F.source.block v) (Arithmetic.context c)
        F.source.columns F.source.columns profiles
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val) =>
      chart.rightCoefficient i) hF.profile (hF.chart v D)
  rw [hfield]
  rfl

theorem key_coefficient_factor (F : FirstPresentation call p) (hF : F.Realizes)
    (key : FirstCauchyKey F) (i : F.source.Column) :
    FirstCauchyKey.coefficient key i = FirstCauchyKey.multiplier key i * F.coefficient i := by
  cases hs : FirstCauchyKey.side key <;>
    simp only [FirstCauchyKey.coefficient, FirstCauchyKey.multiplier,
      FirstCauchyKey.data, hs, Bool.false_eq_true, if_false, if_true] <;>
    split_ifs <;>
    simp only [FirstBlockDirectData.originalLeftCoefficient,
      FirstBlockDirectData.originalRightCoefficient, FirstCauchyKey.piece,
      chart_left_coefficient F hF, chart_right_coefficient F hF] <;> ring

theorem key_column_mem (F : FirstPresentation call p) (key : FirstCauchyKey F)
    (i : F.source.Column) (hi : i ∈ (FirstCauchyKey.data key).columns) : i ∈ F.source.columns := by
  cases hs : FirstCauchyKey.side key
  · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false] at hi
    rw [(FirstCauchyKey.piece key).left_columns] at hi
    exact (Finset.mem_filter.mp hi).1
  · simp only [FirstCauchyKey.data, hs, if_true] at hi
    rw [(FirstCauchyKey.piece key).right_columns] at hi
    exact (Finset.mem_filter.mp hi).1

theorem key_column_norm (F : FirstPresentation call p) (key : FirstCauchyKey F)
    (i : F.source.Column) (hi : i ∈ (FirstCauchyKey.data key).columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) =
      (Ideal.absNorm (selected key).val : ℝ) *
        (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) := by
  cases hs : FirstCauchyKey.side key
  · simp only [FirstCauchyKey.data, selected, hs, Bool.false_eq_true, if_false] at hi ⊢
    rw [(FirstCauchyKey.piece key).left_columns] at hi
    rw [(FirstCauchyKey.piece key).left_ideal]
    change (Ideal.absNorm (F.source.ideal i).val : ℝ) = _
    rw [(FirstCauchyKey.block key).left_reconstruct F.source.columns i hi]
    simp only [map_mul, Nat.cast_mul, (FirstCauchyKey.block key).common_left]
  · simp only [FirstCauchyKey.data, selected, hs, if_true] at hi ⊢
    rw [(FirstCauchyKey.piece key).right_columns] at hi
    rw [(FirstCauchyKey.piece key).right_ideal]
    change (Ideal.absNorm (F.source.ideal i).val : ℝ) = _
    rw [(FirstCauchyKey.block key).right_reconstruct F.source.columns i hi]
    simp only [map_mul, Nat.cast_mul, (FirstCauchyKey.block key).common_right]

theorem source_column_window (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (columnDemand c p frame).Ready call input)
    (F : FirstPresentation call p) (hF : F.Realizes) (key : FirstCauchyKey F)
    (N : F.source.Normalization) (i : F.source.Column)
    (hi : i ∈ (source key N).source.columns)
    (hcoeff : (source key N).source.coefficient i ≠ 0) :
    call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z - idealLogLength call.base (source key N).first.selected.val -
        4 * p.loss) ≤ (Arithmetic.data c).exteriorNorm ((source key N).source.ideal i) ∧
    (Arithmetic.data c).exteriorNorm ((source key N).source.ideal i) ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z - idealLogLength call.base (source key N).first.selected.val +
          4 * p.loss) := by
  have hnonzero : F.coefficient i ≠ 0 := by
    change FirstCauchyKey.coefficient key i ≠ 0 at hcoeff
    rw [key_coefficient_factor F hF key i] at hcoeff
    exact (mul_ne_zero_iff.mp hcoeff).2
  have hfull := source_full_column_window input hframe ready F hF i
    (key_column_mem F key i hi) hnonzero
  have hnorm := key_column_norm F key i hi
  have hlength := rpow_idealLogLength call.base call.domain.scale
    (selected key).val (nonZeroDivisors.coe_ne_zero (selected key))
  rw [← hlength] at hnorm
  let length := idealLogLength call.base (selected key).val
  have hpos : 0 < call.base ^ length := Real.rpow_pos_of_pos call.base_pos _
  constructor
  · apply (mul_le_mul_right hpos).mp
    change call.base ^ (_ - length - 4 * p.loss) * call.base ^ length ≤
      (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) * call.base ^ length
    rw [← Real.rpow_add call.base_pos]
    calc
      _ ≤ call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z - p.loss) :=
        Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (by linarith [p.loss_pos])
      _ ≤ (Arithmetic.data c).exteriorNorm (F.source.ideal i) := hfull.1
      _ = _ := hnorm.trans (mul_comm _ _)
  · apply (mul_le_mul_right hpos).mp
    change (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) * call.base ^ length ≤
      call.base ^ (_ - length + 4 * p.loss) * call.base ^ length
    rw [← Real.rpow_add call.base_pos]
    calc
      _ = (Arithmetic.data c).exteriorNorm (F.source.ideal i) := (hnorm.trans (mul_comm _ _)).symm
      _ ≤ call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + p.loss) := hfull.2
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (by linarith [p.loss_pos])

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.source_full_column_window
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.source_column_window
