import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed norm windows for the original N8a arithmetic carrier

The strict-call domain bounds the original total length, including
centered calls.  The fixed maximal rank annulus bounds every original
profile support.  Their finite products give a uniform power window
for all original columns, including columns whose whole coefficient
vanishes.  Thus no norm-window hypothesis is added to the source task.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

def originalLengthBound (c : TargetContext K) : ℝ :=
  2 + recipeInductionSigma c / 16

theorem originalLengthBound_pos (c : TargetContext K) : 0 < originalLengthBound c := by
  have hs := (recipeInduction_budget (c := c)).1
  dsimp only [originalLengthBound]
  linarith

theorem working_width (call : Call c) :
    call.workingParameters.m + call.workingParameters.q =
      call.node.parameters.m + call.node.parameters.q := by
  dsimp only [Call.workingParameters]
  ring

theorem working_total_le (call : Call c) :
    call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z ≤ originalLengthBound c := by
  have h := call.domain.padded_core
  have hw := call.width_le
  change call.node.parameters.n₁ + call.node.parameters.n₂ +
    call.node.parameters.z ≤ 2 + recipeInductionSigma c / 16
  linarith

theorem original_z_nonneg (call : Call c) : 0 ≤ call.node.parameters.z := by
  rw [call.domain.total_length]
  exact Finset.sum_nonneg (fun i _ => (call.node.data.geometry.slots i).length_pos.le)

theorem original_plain₁_le (call : Call c) :
    call.node.parameters.n₁ ≤ originalLengthBound c := by
  have h := working_total_le call
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _ at h
  linarith [call.domain.plain_right_nonneg, original_z_nonneg call]

theorem original_plain₂_le (call : Call c) :
    call.node.parameters.n₂ ≤ originalLengthBound c := by
  have h := working_total_le call
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _ at h
  linarith [call.domain.plain_left_nonneg, original_z_nonneg call]

theorem original_z_le (call : Call c) : call.node.parameters.z ≤ originalLengthBound c := by
  have h := working_total_le call
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _ at h
  linarith [call.domain.plain_left_nonneg, call.domain.plain_right_nonneg]

theorem slot_length_le (call : Call c) (i : Fin call.localizedData.geometry.slotCount) :
    (call.localizedData.geometry.slots i).length ≤ originalLengthBound c := by
  have h : (call.node.data.geometry.slots i).length ≤ call.node.data.geometry.totalLength :=
    Finset.single_le_sum (fun j _ => (call.node.data.geometry.slots j).length_pos.le)
      (Finset.mem_univ i)
  rw [← call.domain.total_length] at h
  exact h.trans (original_z_le call)

theorem main_left_scale_le (call : Call c) :
    call.base ^ call.workingParameters.n₁ ≤ call.base ^ originalLengthBound c :=
  Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (original_plain₁_le call)

theorem main_right_scale_le (call : Call c) :
    call.base ^ call.workingParameters.n₂ ≤ call.base ^ originalLengthBound c :=
  Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (original_plain₂_le call)

theorem comparison_left_scale_le (call : Call c) :
    call.base ^ call.workingComparison₁ ≤ call.base ^ originalLengthBound c := by
  cases hc : call.node.centered with
  | false => simpa only [Call.workingComparison₁, Call.workingParameters,
      hc, Bool.false_eq_true, ite_false]
      using main_left_scale_le call
  | true =>
    simp only [Call.workingComparison₁, hc, ite_true]
    rw [call.domain.comparison_left hc]
    apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
    exact (call.domain.centered_left hc).trans (original_plain₁_le call)

theorem comparison_right_scale_le (call : Call c) :
    call.base ^ call.workingComparison₂ ≤ call.base ^ originalLengthBound c := by
  cases hc : call.node.centered with
  | false => simpa only [Call.workingComparison₂, Call.workingParameters,
      hc, Bool.false_eq_true, ite_false]
      using main_right_scale_le call
  | true =>
    simp only [Call.workingComparison₂, hc, ite_true]
    rw [call.domain.comparison_right hc]
    apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
    have h := working_total_le call
    change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _ at h
    linarith [call.domain.width_nonneg, original_z_nonneg call]

def annulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (2 * (frame.upper * (2 : ℝ) ^ (6 * (widthBand (recipeInductionSigma c) 2 + 1))))

theorem annulus_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ annulus c frame := le_max_left _ _

theorem upper_le_annulus (input : ProfileInput call) :
    2 * call.prepared.upper ≤ annulus c call.frame := by
  rw [input.regular.upper]
  change 2 * (call.frame.upper * (2 : ℝ) ^ (call.rankBound - call.rank)) ≤
    max 1 (2 * (call.frame.upper * (2 : ℝ) ^ call.rankBound))
  have hpow : (2 : ℝ) ^ (call.rankBound - call.rank) ≤ 2 ^ call.rankBound :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hu : 0 ≤ call.frame.upper := le_trans (by norm_num) call.frame.upper_large
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpow hu) (by norm_num)).trans (le_max_right _ _)

theorem window_le_annulus (input : ProfileInput call) :
    call.window ⊆ Set.Iic (annulus c call.frame) :=
  fun _ hx => hx.2.trans (upper_le_annulus input)

private theorem left_support_norm (input : ProfileInput call)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (scale : ℝ) (hscale : 0 < scale)
    (hI : I ∈ call.localizedData.plainTest₁.support u 0 scale) :
    idealNorm K I ≤ annulus c call.frame * scale := by
  have hprofile := (call.localizedData.plainTest₁.support_spec u 0 scale I).mp hI
  have hrep : input.localized.leftRep u 0 (idealNorm K I / scale) ≠ 0 := by
    simpa only [input.localized.left_eq] using hprofile
  exact (div_le_iff₀ hscale).mp
    (window_le_annulus input (input.localized.left_support u (Set.mem_univ _)
      0 (Set.mem_univ _) hrep))

private theorem right_support_norm (input : ProfileInput call)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (scale : ℝ) (hscale : 0 < scale)
    (hI : I ∈ call.localizedData.plainTest₂.support u 0 scale) :
    idealNorm K I ≤ annulus c call.frame * scale := by
  have hprofile := (call.localizedData.plainTest₂.support_spec u 0 scale I).mp hI
  have hrep : input.localized.rightRep u 0 (idealNorm K I / scale) ≠ 0 := by
    simpa only [input.localized.right_eq] using hprofile
  exact (div_le_iff₀ hscale).mp
    (window_le_annulus input (input.localized.right_support u (Set.mem_univ _)
      0 (Set.mem_univ _) hrep))

theorem left_column_norm (input : ProfileInput call)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ call.workingRaw.leftColumns) :
    idealNorm K I ≤ annulus c call.frame * call.base ^ originalLengthBound c := by
  obtain ⟨u, _, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact (left_support_norm input u I _ (Real.rpow_pos_of_pos call.base_pos _) hI).trans
      (mul_le_mul_of_nonneg_left (main_left_scale_le call)
        (zero_le_one.trans (annulus_one_le c call.frame)))
  · exact (left_support_norm input u I _ (Real.rpow_pos_of_pos call.base_pos _) hI).trans
      (mul_le_mul_of_nonneg_left (comparison_left_scale_le call)
        (zero_le_one.trans (annulus_one_le c call.frame)))

theorem right_column_norm (input : ProfileInput call)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ call.workingRaw.rightColumns) :
    idealNorm K I ≤ annulus c call.frame * call.base ^ originalLengthBound c := by
  obtain ⟨u, _, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact (right_support_norm input u I _ (Real.rpow_pos_of_pos call.base_pos _) hI).trans
      (mul_le_mul_of_nonneg_left (main_right_scale_le call)
        (zero_le_one.trans (annulus_one_le c call.frame)))
  · exact (right_support_norm input u I _ (Real.rpow_pos_of_pos call.base_pos _) hI).trans
      (mul_le_mul_of_nonneg_left (comparison_right_scale_le call)
        (zero_le_one.trans (annulus_one_le c call.frame)))

theorem slot_column_norm (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∈ call.workingRaw.slotColumns i) :
    (Ideal.absNorm P.asIdeal : ℝ) ≤
      annulus c call.frame * call.base ^ originalLengthBound c := by
  have hprofile := ((call.localizedData.geometry.slots i).support_spec 0
    (call.base ^ (call.localizedData.geometry.slots i).length) P).mp hP
  have hrep : input.localized.primeRep i 0
      ((Ideal.absNorm P.asIdeal : ℝ) /
        call.base ^ (call.localizedData.geometry.slots i).length) ≠ 0 := by
    simpa only [input.localized.prime_eq] using hprofile
  have hbound := (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
    (window_le_annulus input
      (input.localized.prime_support i 0 (Set.mem_univ _) hrep))
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (slot_length_le call i))
    (zero_le_one.trans (annulus_one_le c call.frame)))

def normThreshold (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  annulus c frame ^ (c.geometry.slots + 2)

theorem normThreshold_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ normThreshold c frame := one_le_pow₀ (annulus_one_le c frame)

def columnExponent (c : TargetContext K) : ℝ :=
  originalLengthBound c * ((c.geometry.slots + 2 : ℕ) : ℝ) + 1

theorem columnExponent_pos (c : TargetContext K) : 0 < columnExponent c := by
  have h := originalLengthBound_pos c
  dsimp only [columnExponent]
  positivity

theorem original_column_norm (input : ProfileInput call)
    (large : normThreshold c call.frame ≤ call.base)
    (v : call.workingRaw.Column) (hv : v ∈ call.workingRaw.exteriorColumns) :
    (Arithmetic.data c).exteriorNorm (call.workingRaw.columnExterior v) ≤
      call.base ^ columnExponent c := by
  let M : ℝ := annulus c call.frame * call.base ^ originalLengthBound c
  have M_one : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (annulus_one_le c call.frame)
    (Real.one_le_rpow call.domain.scale.le (originalLengthBound_pos c).le)
  have M_nonneg : 0 ≤ M := zero_le_one.trans M_one
  have hcols := (Finset.mem_filter.mp hv).1
  change v ∈ (call.workingRaw.leftColumns.product call.workingRaw.rightColumns).product
    (Fintype.piFinset call.workingRaw.slotColumns) at hcols
  have hp := Finset.mem_product.mp hcols
  have hplain := Finset.mem_product.mp hp.1
  have hslots := Fintype.mem_piFinset.mp hp.2
  have hL := left_column_norm input v.1.1 hplain.1
  have hR := right_column_norm input v.1.2 hplain.2
  have hS : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      M ^ call.localizedData.geometry.slotCount := by
    calc
      _ ≤ ∏ _i : Fin call.localizedData.geometry.slotCount, M :=
        Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
          (fun i _ => slot_column_norm input i (v.2 i) (hslots i))
      _ = _ := by simp
  have hslotsCap : call.localizedData.geometry.slotCount ≤ c.geometry.slots := call.slots_le
  have hpowers : (call.base ^ originalLengthBound c) ^ (c.geometry.slots + 2) =
      call.base ^ (originalLengthBound c * ((c.geometry.slots + 2 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul call.base_pos.le, Real.rpow_natCast]
  change (Ideal.absNorm (call.workingRaw.columnExterior v).val : ℝ) ≤ _
  rw [call.workingRaw.columnExterior_val_of_mem v hv]
  simp only [ParentRawAtoms.columnIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
  calc
    _ ≤ (M * M) * M ^ call.localizedData.geometry.slotCount :=
      mul_le_mul (mul_le_mul hL hR (Nat.cast_nonneg _) M_nonneg) hS
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)) (mul_nonneg M_nonneg M_nonneg)
    _ = M ^ (call.localizedData.geometry.slotCount + 2) := by
      rw [pow_add, pow_two]
      ring
    _ ≤ M ^ (c.geometry.slots + 2) :=
      pow_le_pow_right₀ M_one (Nat.add_le_add_right hslotsCap 2)
    _ = normThreshold c call.frame *
        call.base ^ (originalLengthBound c * ((c.geometry.slots + 2 : ℕ) : ℝ)) := by
      dsimp only [M, normThreshold]
      rw [mul_pow, hpowers]
    _ ≤ call.base * call.base ^
        (originalLengthBound c * ((c.geometry.slots + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right large (Real.rpow_nonneg call.base_pos.le _)
    _ = call.base ^ columnExponent c := by
      rw [show columnExponent c =
        1 + originalLengthBound c * ((c.geometry.slots + 2 : ℕ) : ℝ) by
          dsimp only [columnExponent]; ring,
        Real.rpow_add call.base_pos, Real.rpow_one]

theorem first_source_norm {p : SourceParameters c}
    (input : ProfileInput call) (large : normThreshold c call.frame ≤ call.base)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ columnExponent c := by
  rw [hF.ideal i]
  apply original_column_norm input large
  rw [← hF.columns]
  exact Finset.mem_map_of_mem F.index.toEmbedding hi

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.working_total_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_column_norm
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.first_source_norm
