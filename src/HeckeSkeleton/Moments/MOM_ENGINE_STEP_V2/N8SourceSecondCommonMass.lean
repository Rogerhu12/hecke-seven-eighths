module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceUniformDecorations
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceFrozenDivisor

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual second common sum retains the first-divisor density

The original active common pairs satisfy the first residual divisor's
literal divisibility conditions.  Their harmonic sum is combined with
the actual source-class decorations and both inner-divisor allocation
families.  All three constants precede the call and its physical labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance n8SecondCommonMassCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PhysicalSource

variable (source : PhysicalSource call p)

theorem activeCommon_subset : source.activeCommon ⊆
    commonSupportPool source.source.columns source.source.columns
      (fun j => (source.source.ideal j).val) (fun j => (source.source.ideal j).val) := by
  intro DE hDE
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hDE
  exact Finset.mem_image.mpr ⟨ij, Finset.mem_product.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hij).1).1,
      (Finset.mem_filter.mp (Finset.mem_product.mp hij).2).1⟩, rfl⟩

def commonIndexMass : ℝ :=
  ∑ DE ∈ source.activeCommon, 1 / (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ)

theorem commonIndexMass_nonneg : 0 ≤ source.commonIndexMass :=
  Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _))

end PhysicalSource

namespace SecondSource

variable (source : SecondSource call p) (LC RC : OriginalCover source.physical)

theorem sum_activeCommon (f : (Ideal (𝓞 K) × Ideal (𝓞 K)) → ℝ) :
    (∑ DE : source.CommonLabel,
      if DE.val ∈ source.physical.activeCommon then f DE.val else 0) =
      ∑ DE ∈ source.physical.activeCommon, f DE := by
  let pool := commonSupportPool source.physical.source.columns
    source.physical.source.columns (fun j => (source.physical.source.ideal j).val)
    (fun j => (source.physical.source.ideal j).val)
  calc
    _ = ∑ DE ∈ pool,
        if DE ∈ source.physical.activeCommon then f DE else 0 :=
      Finset.sum_coe_sort pool _
    _ = ∑ DE ∈ source.physical.activeCommon, f DE := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext DE
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨source.physical.activeCommon_subset h, h⟩⟩

/-- The literal second-class carrier, after summing its actual
independent divisor and both occurrence allocations. -/
def classIndexMass : ℝ :=
  ∑ DE : source.CommonLabel,
    if DE.val ∈ source.physical.activeCommon then
      (1 / (Ideal.absNorm (commonRadical DE.val.1 DE.val.2) : ℝ)) *
        ∑ d : source.CommonDecoration LC RC DE,
          SourceClassKey.allocationIndexMass (source := source)
            (LC := LC) (RC := RC) ⟨DE, d⟩
    else 0

theorem classIndexMass_nonneg : 0 ≤ source.classIndexMass LC RC := by
  apply Finset.sum_nonneg
  intro DE _
  split_ifs
  · exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => SourceClassKey.allocationIndexMass_nonneg _))
  · exact le_rfl

end SecondSource

namespace N8Source

theorem pair_harmonic_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ S : Ideal (𝓞 K),
      Squarefree S → S ≠ 0 → ∀ pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)),
      (∀ DE ∈ pairs, Valid S (DE, ∅)) →
      (∀ DE ∈ pairs, (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ B) →
      (∑ DE ∈ pairs, 1 / (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ)) ≤
        C * Z ^ ε / (Ideal.absNorm S : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := common_radical_harmonic_mass (K := K) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ S hS hS0 pairs hvalid hnorm
  have h := hmass Z hZ S hS hS0
    (pairs.image (fun DE => (DE, (∅ : Finset (Ideal (𝓞 K))))))
    (by
      intro v hv
      obtain ⟨DE, hDE, rfl⟩ := Finset.mem_image.mp hv
      exact hvalid DE hDE)
    (by
      intro v hv
      obtain ⟨DE, hDE, rfl⟩ := Finset.mem_image.mp hv
      exact hnorm DE hDE)
  rw [Finset.sum_image (fun a _ b _ hab => congrArg Prod.fst hab)] at h
  exact h

theorem original_second_common_mass (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (trace : SourceTrace call p), trace.Realizes →
      ∀ i : Fin trace.expansion.count,
      0 < (trace.second.source i).physical.outerWeight →
      (trace.second.source i).physical.source.rows.Nonempty →
      (trace.second.source i).physical.commonIndexMass ≤
        C * call.base ^ ε /
          (Ideal.absNorm (trace.second.source i).physical.first.residualDivisor.val : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := pair_harmonic_mass (K := K) (columnExponent c) ε
    (columnExponent_pos c).le hε
  refine ⟨C, hC, ?_⟩
  intro call input large p trace htrace i hpos hrows
  have hbase_pos : 0 < call.base := call.base_pos
  have hpos' : 0 < (trace.expansion.source i).outerWeight := by
    exact Eq.mp (congrArg (fun s : PhysicalSource call p => 0 < s.outerWeight)
      (htrace.second.physical i)) hpos
  have hrows' : (trace.expansion.source i).source.rows.Nonempty := by
    exact Eq.mp (congrArg (fun s : PhysicalSource call p => s.source.rows.Nonempty)
      (htrace.second.physical i)) hrows
  have hs : Squarefree (trace.second.source i).physical.first.residualDivisor.val := by
    exact Eq.mpr (congrArg
      (fun s : PhysicalSource call p => Squarefree s.first.residualDivisor.val)
      (htrace.second.physical i))
      (trace.expansion.residual_squarefree htrace.cauchy htrace.expansion i hpos')
  have hd : ∀ j, (trace.second.source i).physical.source.coefficient j ≠ 0 →
      (trace.second.source i).physical.first.residualDivisor.val ∣
        ((trace.second.source i).physical.source.ideal j).val := by
    let property (s : PhysicalSource call p) : Prop :=
      ∀ j : s.Column, s.source.coefficient j ≠ 0 →
        s.first.residualDivisor.val ∣ (s.source.ideal j).val
    have hs : property (trace.expansion.source i) :=
      trace.expansion.residual_dvd htrace.cauchy htrace.expansion i hrows'
    exact Eq.mpr (congrArg property (htrace.second.physical i)) hs
  apply hmass call.base call.domain.scale.le _ hs
    (nonZeroDivisors.coe_ne_zero (trace.second.source i).physical.first.residualDivisor)
    (trace.second.source i).physical.activeCommon
    ((trace.second.source i).physical.activeCommon_valid hs hd)
  intro DE hDE
  exact trace.second.common_norm input large htrace.first htrace.cauchy
    htrace.expansion htrace.second i
      ⟨DE, (trace.second.source i).physical.activeCommon_subset hDE⟩

set_option maxHeartbeats 1000000 in
/-- The entire second source-class carrier has the original first
divisor's harmonic density, with no aggregate mass hypothesis. -/
theorem original_second_class_mass (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (trace : SourceTrace call p), trace.Realizes →
      ∀ (i : Fin trace.expansion.count)
        (LC RC : OriginalCover (trace.second.source i).physical),
        LC.Realizes → RC.Realizes →
        0 < (trace.second.source i).physical.outerWeight →
        (trace.second.source i).physical.source.rows.Nonempty →
        (trace.second.source i).classIndexMass LC RC ≤
          C * call.base ^ ε /
            (Ideal.absNorm (trace.second.source i).physical.first.residualDivisor.val : ℝ) := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, halloc⟩ := original_allocation_index_mass c δ hδ
  obtain ⟨D, hD, hdec⟩ := original_class_decoration_subpower c δ hδ
  obtain ⟨H, hH, hcommon⟩ := original_second_common_mass c δ hδ
  refine ⟨D * A * H, by positivity, ?_⟩
  intro call input large p trace htrace i LC RC hLC hRC hpos hrows
  have hbase_pos : 0 < call.base := call.base_pos
  let M : ℝ := D * A * call.base ^ (2 * δ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hinner (DE : (trace.second.source i).CommonLabel) :
      (∑ d : (trace.second.source i).CommonDecoration LC RC DE,
        SourceClassKey.allocationIndexMass (source := trace.second.source i)
          (LC := LC) (RC := RC) ⟨DE, d⟩) ≤ M := by
    calc
      _ ≤ ∑ _d : (trace.second.source i).CommonDecoration LC RC DE,
          A * call.base ^ δ := by
        apply Finset.sum_le_sum
        intro d _
        exact halloc call input large p trace htrace i LC RC hLC hRC ⟨DE, d⟩
      _ = (Fintype.card ((trace.second.source i).CommonDecoration LC RC DE) : ℝ) *
          (A * call.base ^ δ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (D * call.base ^ δ) * (A * call.base ^ δ) :=
        mul_le_mul_of_nonneg_right
          (hdec call input large p trace htrace i LC RC hLC hRC DE) (by positivity)
      _ = M := by
        dsimp only [M]
        rw [show 2 * δ = δ + δ by ring, Real.rpow_add call.base_pos]
        ring
  have hclass : (trace.second.source i).classIndexMass LC RC ≤
      M * (trace.second.source i).physical.commonIndexMass := by
    calc
      _ ≤ ∑ DE : (trace.second.source i).CommonLabel,
          if DE.val ∈ (trace.second.source i).physical.activeCommon then
            (1 / (Ideal.absNorm (commonRadical DE.val.1 DE.val.2) : ℝ)) * M
          else 0 := by
        apply Finset.sum_le_sum
        intro DE _
        by_cases hDE : DE.val ∈ (trace.second.source i).physical.activeCommon
        · simp only [if_pos hDE]
          exact mul_le_mul_of_nonneg_left (hinner DE)
            (one_div_nonneg.mpr (Nat.cast_nonneg _))
        · simp only [if_neg hDE]
          exact le_rfl
      _ = M * (trace.second.source i).physical.commonIndexMass := by
        calc
          _ = ∑ DE ∈ (trace.second.source i).physical.activeCommon,
              (1 / (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ)) * M :=
            (trace.second.source i).sum_activeCommon
              (fun DE => (1 / (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ)) * M)
          _ = _ := by
            simp only [PhysicalSource.commonIndexMass, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro DE _
            exact mul_comm _ _
  apply (hclass.trans (mul_le_mul_of_nonneg_left
    (hcommon call input large p trace htrace i hpos hrows) hM)).trans_eq
  dsimp only [M]
  have he : ε = 2 * δ + δ := by dsimp [δ]; ring
  rw [he, Real.rpow_add call.base_pos]
  ring

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_second_common_mass
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_second_class_mass
