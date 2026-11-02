import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleCompensation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOriginalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A uniform norm bound on the original first Cartesian carrier

Each plain carrier is the union of the two original comparison
supports. Both original scales are bounded by the full plain scale;
this deliberately allows mixed comparison coordinates in the carrier.
Every surviving original prime occurrence is then included once.
The resulting bound applies before any nonzero-column restriction.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace T3b

def firstColumnAnnulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  profileAnnulus c frame ^ (c.geometry.slots + 2)

theorem firstColumnAnnulus_one_le : 1 ≤ firstColumnAnnulus c call.frame :=
  one_le_pow₀ (profileAnnulus_one_le c call.frame)

end T3b

namespace Call

variable (call : Call c)

theorem t3b_plainScale_le (rectangle plain : Bool) :
    call.originalPlainScale rectangle plain ≤
      call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂) := by
  have hleft := call.domain.plain_left_nonneg
  have hright := call.domain.plain_right_nonneg
  cases rectangle with
  | false =>
    cases plain <;>
      apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le <;>
      dsimp only [originalPlainScale, Bool.false_eq_true, if_false, if_true] <;> linarith
  | true =>
    cases hc : call.node.centered with
    | false =>
      cases plain <;>
        simp only [originalPlainScale, workingComparison₁, workingComparison₂,
          hc, Bool.false_eq_true, if_false, if_true] <;>
        apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le <;> linarith
    | true =>
      cases plain with
      | false =>
        change call.base ^ call.workingComparison₁ ≤ _
        simp only [workingComparison₁, hc, if_true]
        rw [call.domain.comparison_left hc]
        apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        linarith [call.domain.centered_left hc]
      | true =>
        change call.base ^ call.workingComparison₂ ≤ _
        simp only [workingComparison₂, hc, if_true]
        rw [call.domain.comparison_right hc]
        apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        linarith [call.domain.width_nonneg]

private theorem left_norm_le_of_support (input : ProfileInput call)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (N : ℝ) (hN : 0 < N)
    (hI : I ∈ call.localizedData.plainTest₁.support u 0 N) :
    idealNorm K I ≤ T3b.profileAnnulus c call.frame * N := by
  have hp := (call.localizedData.plainTest₁.support_spec u 0 N I).mp hI
  have hr : input.localized.leftRep u 0 (idealNorm K I / N) ≠ 0 := by
    simpa only [input.localized.left_eq] using hp
  have hw := input.localized.left_support u (Set.mem_univ _) 0 (Set.mem_univ _) hr
  exact (div_le_iff₀ hN).mp
    (T3b.profileWindow_upper c call.frame (call.t3b_window_subset input hw))

private theorem right_norm_le_of_support (input : ProfileInput call)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (N : ℝ) (hN : 0 < N)
    (hI : I ∈ call.localizedData.plainTest₂.support u 0 N) :
    idealNorm K I ≤ T3b.profileAnnulus c call.frame * N := by
  have hp := (call.localizedData.plainTest₂.support_spec u 0 N I).mp hI
  have hr : input.localized.rightRep u 0 (idealNorm K I / N) ≠ 0 := by
    simpa only [input.localized.right_eq] using hp
  have hw := input.localized.right_support u (Set.mem_univ _) 0 (Set.mem_univ _) hr
  exact (div_le_iff₀ hN).mp
    (T3b.profileWindow_upper c call.frame (call.t3b_window_subset input hw))

theorem t3b_leftCarrier_norm_le (input : ProfileInput call)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ call.workingRaw.leftColumns) :
    idealNorm K I ≤ T3b.profileAnnulus c call.frame *
      call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂) := by
  obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hu with hu | hu
  · exact (call.left_norm_le_of_support input u I _
      (Real.rpow_pos_of_pos call.base_pos _) hu).trans
      (mul_le_mul_of_nonneg_left (call.t3b_plainScale_le false false)
        (T3b.profileAnnulus_pos c call.frame).le)
  · exact (call.left_norm_le_of_support input u I _
      (Real.rpow_pos_of_pos call.base_pos _) hu).trans
      (mul_le_mul_of_nonneg_left (call.t3b_plainScale_le true false)
        (T3b.profileAnnulus_pos c call.frame).le)

theorem t3b_rightCarrier_norm_le (input : ProfileInput call)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ call.workingRaw.rightColumns) :
    idealNorm K I ≤ T3b.profileAnnulus c call.frame *
      call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂) := by
  obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hu with hu | hu
  · exact (call.right_norm_le_of_support input u I _
      (Real.rpow_pos_of_pos call.base_pos _) hu).trans
      (mul_le_mul_of_nonneg_left (call.t3b_plainScale_le false true)
        (T3b.profileAnnulus_pos c call.frame).le)
  · exact (call.right_norm_le_of_support input u I _
      (Real.rpow_pos_of_pos call.base_pos _) hu).trans
      (mul_le_mul_of_nonneg_left (call.t3b_plainScale_le true true)
        (T3b.profileAnnulus_pos c call.frame).le)

theorem t3b_slotCarrier_norm_le (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ call.workingRaw.slotColumns i) :
    (Ideal.absNorm q.asIdeal : ℝ) ≤
      T3b.profileAnnulus c call.frame * call.base ^ call.originalLength i := by
  have hp := ((call.localizedData.geometry.slots i).support_spec 0
    (call.base ^ call.originalLength i) q).mp hq
  have hr : input.localized.primeRep i 0
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i) ≠ 0 := by
    simpa only [input.localized.prime_eq] using hp
  have hw := input.localized.prime_support i 0 (Set.mem_univ _) hr
  exact (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
    (T3b.profileWindow_upper c call.frame (call.t3b_window_subset input hw))

theorem t3b_columnCarrier_norm_le (input : ProfileInput call)
    (v : call.workingRaw.Column) (hv : v ∈ call.workingRaw.exteriorColumns) :
    (Arithmetic.data c).exteriorNorm (call.workingRaw.columnExterior v) ≤
      T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z)) := by
  let C := T3b.profileAnnulus c call.frame
  have hC : 1 ≤ C := T3b.profileAnnulus_one_le c call.frame
  have htuple := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
  have hplain := Finset.mem_product.mp htuple.1
  have hl := call.t3b_leftCarrier_norm_le input v.1.1 hplain.1
  have hr := call.t3b_rightCarrier_norm_le input v.1.2 hplain.2
  have hp : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      C ^ call.localizedData.geometry.slotCount * (∏ i, call.base ^ call.originalLength i) := by
    calc
      _ ≤ ∏ i, C * call.base ^ call.originalLength i :=
        Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
          (fun i _ => call.t3b_slotCarrier_norm_le input i (v.2 i)
            (Fintype.mem_piFinset.mp htuple.2 i))
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  have hprime : (∏ i, call.base ^ call.originalLength i) =
      call.base ^ call.node.parameters.z := by
    rw [← Real.rpow_sum_of_pos call.base_pos]
    congr 1
    exact call.domain.total_length.symm
  have hz : 0 ≤ call.node.parameters.z := by
    rw [call.domain.total_length]
    exact Finset.sum_nonneg (fun i _ => (call.node.data.geometry.slots i).length_pos.le)
  change (Ideal.absNorm (call.workingRaw.columnExterior v).val : ℝ) ≤ _
  rw [call.workingRaw.columnExterior_val_of_mem v hv]
  simp only [ParentRawAtoms.columnIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
  calc
    _ ≤ (C * call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂)) *
        (C * call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂)) *
        (C ^ call.localizedData.geometry.slotCount *
          (∏ i, call.base ^ call.originalLength i)) :=
      mul_le_mul
        (mul_le_mul hl hr (idealNorm_pos K v.1.2).le
          (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg call.base_pos.le _)))
        hp (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg call.base_pos.le _))
          (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg call.base_pos.le _)))
    _ = C ^ (call.localizedData.geometry.slotCount + 2) *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂) +
          call.node.parameters.z) := by
      have hpow : call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂) +
          call.node.parameters.z) =
          call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂) *
          call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂) *
          call.base ^ call.node.parameters.z := by
        rw [Real.rpow_add call.base_pos
          (2 * (call.node.parameters.n₁ + call.node.parameters.n₂)) call.node.parameters.z,
          two_mul, Real.rpow_add call.base_pos
            (call.node.parameters.n₁ + call.node.parameters.n₂)
            (call.node.parameters.n₁ + call.node.parameters.n₂)]
      rw [hprime, hpow, pow_add, pow_two]
      ring
    _ ≤ _ :=
      mul_le_mul
        (pow_le_pow_right₀ hC (Nat.add_le_add_right call.slots_le 2))
        (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (by linarith))
        (Real.rpow_nonneg call.base_pos.le _)
        (pow_nonneg (zero_le_one.trans hC) _)

end Call

namespace FirstPresentation

variable (F : FirstPresentation call p) (hF : F.Realizes)
variable (input : ProfileInput call)

theorem t3b_column_norm_le (i : F.source.Column) (hi : i ∈ F.source.columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤
      T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z)) := by
  rw [hF.ideal i]
  apply call.t3b_columnCarrier_norm_le input (F.index i)
  rw [← hF.columns]
  exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

theorem t3b_common_norm_le (v : F.source.CommonLabel) :
    (Ideal.absNorm v.val.1 : ℝ) ≤ T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z)) ∧
    (Ideal.absNorm v.val.2 : ℝ) ≤ T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z)) := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp v.property
  have hl := F.t3b_column_norm_le hF input ij.1 (Finset.mem_product.mp hij).1
  have hr := F.t3b_column_norm_le hF input ij.2 (Finset.mem_product.mp hij).2
  have hb := actual_common_label_norm_le (F.source.ideal ij.1).val
    (F.source.ideal ij.2).val (F.source.ideal ij.1).property.1
    (F.source.ideal ij.2).property.1
  rw [he] at hb
  exact ⟨hb.1.trans hl, hb.2.trans hr⟩

theorem t3b_firstDivisor_norm_le (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (Ideal.absNorm (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val : ℝ) ≤
      T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z)) :=
  (norm_le_of_dvd
    (by rw [← (F.source.block v).common_left]; exact (primePowerProduct _ _).property.1)
    (F.t3b_firstDivisor_dvd_left hF v D)).trans (F.t3b_common_norm_le hF input v).1

theorem t3b_firstActive_norm_le (v : F.source.CommonLabel) :
    (Ideal.absNorm (firstActiveRadical v.val.1 v.val.2) : ℝ) ≤
      T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z)) := by
  have hleft : v.val.1 ≠ 0 := by
    rw [← (F.source.block v).common_left]
    exact (primePowerProduct _ _).property.1
  exact (norm_le_of_dvd hleft (T3b.firstActiveRadical_dvd_left _ _ hleft)).trans
    (F.t3b_common_norm_le hF input v).1

/-- A fixed threshold can absorb only the fixed annulus. The complete
carrier, physical divisor and first active radical remain unchanged. -/
theorem t3b_firstLengths_le (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (error : ℝ)
    (hannulus : T3b.firstColumnAnnulus c call.frame ≤ call.base ^ error) :
    idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val +
      idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) ≤
        4 * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) +
          2 * error := by
  have hnorm (I : Ideal (𝓞 K)) (hI : I ≠ 0)
      (hi : (Ideal.absNorm I : ℝ) ≤ T3b.firstColumnAnnulus c call.frame *
        call.base ^ (2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z))) :
      idealLogLength call.base I ≤
        error + 2 * (call.node.parameters.n₁ + call.node.parameters.n₂ +
          call.node.parameters.z) := by
    apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
    rw [rpow_idealLogLength call.base call.domain.scale I hI,
      Real.rpow_add call.base_pos]
    exact hi.trans (mul_le_mul_of_nonneg_right hannulus (Real.rpow_nonneg call.base_pos.le _))
  have hD := hnorm _ (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).property.1
    (F.t3b_firstDivisor_norm_le hF input v D)
  have hR := hnorm _ (firstActiveRadical_ne_zero _ _) (F.t3b_firstActive_norm_le hF input v)
  linarith

theorem t3b_firstTilt_le (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset)
    (hannulus : T3b.firstColumnAnnulus c call.frame ≤ call.base) :
    p.tilt *
      (idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val -
        call.workingParameters.m +
        idealLogLength call.base (firstActiveRadical v.val.1 v.val.2)) ≤
      p.loss * (10 + recipeInductionSigma c / 4) := by
  have he := F.t3b_firstLengths_le hF input v D 1
    (by simpa only [Real.rpow_one] using hannulus)
  have hm := call.t3b_working_m_nonneg hF.active
  have hA := call.t3b_totalLength_le
  have hbound :
      idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val -
        call.workingParameters.m +
        idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) ≤
          10 + recipeInductionSigma c / 4 := by
    change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤
      2 + recipeInductionSigma c / 16 at hA
    linarith
  have hpositive : 0 ≤ 10 + recipeInductionSigma c / 4 := by
    have hs := (recipeInduction_budget (c := c)).1
    positivity
  exact (mul_le_mul_of_nonneg_left hbound p.tilt_pos.le).trans
    (mul_le_mul_of_nonneg_right p.tilt_le_loss hpositive)

theorem t3b_firstTilt_rpow_le (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset)
    (hannulus : T3b.firstColumnAnnulus c call.frame ≤ call.base) :
    call.base ^ (p.tilt *
      (idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val -
        call.workingParameters.m +
        idealLogLength call.base (firstActiveRadical v.val.1 v.val.2))) ≤
      call.base ^ (p.loss * (10 + recipeInductionSigma c / 4)) :=
  Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
    (F.t3b_firstTilt_le hF input v D hannulus)

end FirstPresentation

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstPresentation.t3b_firstLengths_le
