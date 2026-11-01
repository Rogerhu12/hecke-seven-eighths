import HeckeSkeleton.HighBin
import HeckeSkeleton.ExpansionModels.ActualRecipeEstimates

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton
open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

-- Base elaborated the recipe parameters under these two local instances.
attribute [local instance] expansionNormOneSpace expansionNormOneBorel

-- OBLIGATION EX-HEIGHT-BUDGET | revised Proposition 6.3, §8 (pp.41–42,49–51).
-- Internal degree and ceiling are selected before tau or the external tail order.
def expansionBudget (c : TargetContext K) : {b : ℝ × ℝ // 0 ≤ b.1 ∧ 0 < b.2} := by
  exact ⟨((expansionRetainedData K c).2.2, (expansionPhysicalParameters K c).ceiling),
    (expansionRetainedData_spec K c).2.2.1, (expansionPhysicalParameters K c).ceiling_pos⟩

/-- The source threshold is selected only after tau, from the proved
detector theorem for this same raw recipe. The other parameters are fixed. -/
def expansionSourceCutoff (c : TargetContext K) (τ : ℝ) : ℝ :=
  if h : 0 < τ ∧ τ ≤ (expansionPhysicalParameters K c).ceiling then
    Classical.choose (expansionRecipeRaw_source K c τ h.1 h.2)
  else 2

theorem expansionSourceCutoff_ge_two (c : TargetContext K) (τ : ℝ) :
    2 ≤ expansionSourceCutoff K c τ := by
  unfold expansionSourceCutoff
  split_ifs with h
  · exact (Classical.choose_spec (expansionRecipeRaw_source K c τ h.1 h.2)).1
  · exact le_rfl

theorem expansionSourceCutoff_source (c : TargetContext K) (τ : ℝ)
    (hτ : 0 < τ) (hc : τ ≤ (expansionBudget K c).val.2) :
    ∀ Z : ℝ, expansionSourceCutoff K c τ ≤ Z → ∀ b,
      BlockSource c.geometry ((highExpansion K c Z (Z ^ τ)).block b)
        c.family.B c.family.lamA (expansionPhysicalParameters K c).k Z := by
  have h : 0 < τ ∧ τ ≤ (expansionPhysicalParameters K c).ceiling := ⟨hτ, hc⟩
  simpa only [expansionSourceCutoff, dif_pos h] using
    (Classical.choose_spec (expansionRecipeRaw_source K c τ h.1 h.2)).2

-- OBLIGATION EX-CUTOFFS | revised Proposition 6.3, §8 (pp.41–42,49–51).
-- One constant/threshold for the complete moving label and contour family.
-- The remaining analytic choice is kept explicit. Its deterministic envelope
-- below is the only public cutoff pair used by every expansion component.
def expansionCutoffsRaw (c : TargetContext K) (τ : ℝ) :
    {b : ℝ × ℝ // 2 ≤ b.1 ∧ 0 ≤ b.2} := by
  exact ⟨(max (expansionSourceCutoff K c τ) (expansionRetainedData K c).2.1,
      max (expansionRetainedData K c).1 (expansionPhysicalParameters K c).k),
    (expansionSourceCutoff_ge_two K c τ).trans (le_max_left _ _),
    (expansionRetainedData_spec K c).1.le.trans (le_max_left _ _)⟩

/-- The literal retained shell schedule has one fixed buffered multiplicity.
Amplitude labels and witness subdivisions are counted separately. -/
def expansionBlockCountConstant (c : TargetContext K) : ℝ :=
  ((expansionRecipeRaw K c).bufferMultiplicity : ℝ) *
    (2 + (((13 / 16 + expansionShellAllowance K c) - 1 / 16) / Real.log 2) / c.lamB)

/-- One common pair for all five bounds. The small-scale guard and the
height-free block count require these explicit lower envelopes. -/
def expansionCutoffs (c : TargetContext K) (τ : ℝ) :
    {b : ℝ × ℝ // 2 ≤ b.1 ∧ 0 ≤ b.2} :=
  ⟨(max (expansionCutoffsRaw K c τ).val.1 ((2 : ℝ) ^ 16),
      max (expansionCutoffsRaw K c τ).val.2 (expansionBlockCountConstant K c)),
    (expansionCutoffsRaw K c τ).property.1.trans (le_max_left _ _),
    (expansionCutoffsRaw K c τ).property.2.trans (le_max_left _ _)⟩

theorem expansionCutoffs_threshold_guard (c : TargetContext K) (τ : ℝ) :
    (2 : ℝ) ^ 16 ≤ (expansionCutoffs K c τ).val.1 := le_max_right _ _

theorem expansionCutoffs_count_constant (c : TargetContext K) (τ : ℝ) :
    expansionBlockCountConstant K c ≤ (expansionCutoffs K c τ).val.2 := le_max_right _ _

theorem expansionCutoffs_dominates_raw (c : TargetContext K) (τ : ℝ) :
    (expansionCutoffsRaw K c τ).val.1 ≤ (expansionCutoffs K c τ).val.1 ∧
      (expansionCutoffsRaw K c τ).val.2 ≤ (expansionCutoffs K c τ).val.2 :=
  ⟨le_max_left _ _, le_max_left _ _⟩

theorem expansionCutoffs_retained_threshold (c : TargetContext K) (τ : ℝ) :
    (expansionRetainedData K c).2.1 ≤ (expansionCutoffs K c τ).val.1 :=
  (le_max_right _ _).trans (expansionCutoffs_dominates_raw K c τ).1

theorem expansionCutoffs_source_threshold (c : TargetContext K) (τ : ℝ) :
    expansionSourceCutoff K c τ ≤ (expansionCutoffs K c τ).val.1 :=
  (le_max_left _ _).trans (expansionCutoffs_dominates_raw K c τ).1

theorem expansionCutoffs_retained_constant (c : TargetContext K) (τ : ℝ) :
    (expansionRetainedData K c).1 ≤ (expansionCutoffs K c τ).val.2 :=
  (le_max_left _ _).trans (expansionCutoffs_dominates_raw K c τ).2

theorem expansionCutoffs_source_constant (c : TargetContext K) (τ : ℝ) :
    (expansionPhysicalParameters K c).k ≤ (expansionCutoffs K c τ).val.2 :=
  (le_max_right _ _).trans (expansionCutoffs_dominates_raw K c τ).2

/-- D-EXPANSION's actual block count satisfies the required bound with no
height factor. This statement is independent of every analytic estimate. -/
theorem highExpansion_blockCount_bound (c : TargetContext K) (Z T : ℝ)
    (hZ : 1 ≤ Z) :
    ((highExpansion K c Z T).blockCount : ℝ) ≤
      expansionBlockCountConstant K c * Z ^ c.lamB := by
  have hzeta : 0 < expansionShellAllowance K c :=
    (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).1
  have hcount := highExpansion_blockCount_le_schedule K c Z T
  change (highExpansion K c Z T).blockCount ≤
    ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + expansionShellAllowance K c) *
      (expansionRecipeRaw K c).bufferMultiplicity at hcount
  have hcount' : ((highExpansion K c Z T).blockCount : ℝ) ≤
      (ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + expansionShellAllowance K c) : ℝ) *
        (expansionRecipeRaw K c).bufferMultiplicity := by
    exact_mod_cast hcount
  have hshell := ExpansionInterfaces.shellCount_subpower hZ
    (show (1 / 16 : ℝ) ≤ 13 / 16 + expansionShellAllowance K c by linarith) c.lamB_pos
  calc
    _ ≤ (ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + expansionShellAllowance K c) : ℝ) *
        (expansionRecipeRaw K c).bufferMultiplicity := hcount'
    _ ≤ (2 + (((13 / 16 + expansionShellAllowance K c) - 1 / 16) / Real.log 2) / c.lamB) *
        Z ^ c.lamB * (expansionRecipeRaw K c).bufferMultiplicity :=
      mul_le_mul_of_nonneg_right hshell (Nat.cast_nonneg _)
    _ = _ := by unfold expansionBlockCountConstant; ring

-- OBLIGATION EX-IDENTITY | revised Proposition 6.3, §7 (pp.41–49).
-- Blocks are the shifted fixed-bin contributions. The whole-bin contour
-- differences are part of this SAME expansion's tail, before label splitting.
theorem expansion_identity (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    (targetData K c).probeFunction (targetCharacter K c) Z -
      (targetData K c).signal (targetCharacter K c) Z =
    (highExpansion K c Z (Z ^ τ)).principal + (highExpansion K c Z (Z ^ τ)).small +
      (highExpansion K c Z (Z ^ τ)).large +
      (∑ b, ((highExpansion K c Z (Z ^ τ)).block b).value) +
      (highExpansion K c Z (Z ^ τ)).tail := by
  have hZtwo : 2 ≤ Z := (expansionCutoffs K c τ).property.1.trans hZ
  exact expansionRecipeRaw_identity K c Z (Z ^ τ)
    ((expansionCutoffs_threshold_guard K c τ).trans hZ)
    (Real.one_le_rpow (by linarith) hτ.le)

-- OBLIGATION EX-PRINCIPAL | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_principal (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).principal‖ ≤
    (expansionCutoffs K c τ).val.2 *
      (Z ^ (c.family.B - 11 / 16 - 23 / 960 + c.lamB) +
       Z ^ (c.family.B - 11 / 16 - 13 / 9600 + c.lamB) +
       Z ^ (c.family.B - 11 / 16 - principalSlotSaving c.geometry + c.lamB)) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1 := by
  have hZtwo : 2 ≤ Z := (expansionCutoffs K c τ).property.1.trans hZ
  have hH : 1 ≤ Z ^ τ := Real.one_le_rpow (by linarith) hτ.le
  have hb := ((expansionRetainedData_spec K c).2.2.2 Z (Z ^ τ)
    ((expansionCutoffs_retained_threshold K c τ).trans hZ) hH).1
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (expansionCutoffs_retained_constant K c τ) (by positivity))
    (by positivity)

-- OBLIGATION EX-SMALL | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_small (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).small‖ ≤
    (expansionCutoffs K c τ).val.2 * Z ^ (c.family.B - 11 / 16 - 1 / 50 + c.lamB) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1 := by
  have hZtwo : 2 ≤ Z := (expansionCutoffs K c τ).property.1.trans hZ
  have hH : 1 ≤ Z ^ τ := Real.one_le_rpow (by linarith) hτ.le
  have hb := ((expansionRetainedData_spec K c).2.2.2 Z (Z ^ τ)
    ((expansionCutoffs_retained_threshold K c τ).trans hZ) hH).2.1
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (expansionCutoffs_retained_constant K c τ) (by positivity))
    (by positivity)

-- OBLIGATION EX-LARGE | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_large (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).large‖ ≤
    (expansionCutoffs K c τ).val.2 * Z ^ (c.family.B - 11 / 16 - 63 / 800 + c.lamB) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1 := by
  have hZtwo : 2 ≤ Z := (expansionCutoffs K c τ).property.1.trans hZ
  have hH : 1 ≤ Z ^ τ := Real.one_le_rpow (by linarith) hτ.le
  have hb := ((expansionRetainedData_spec K c).2.2.2 Z (Z ^ τ)
    ((expansionCutoffs_retained_threshold K c τ).trans hZ) hH).2.2
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (expansionCutoffs_retained_constant K c τ) (by positivity))
    (by positivity)

-- OBLIGATION EX-BLOCK-COUNT | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_blockCount (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ((highExpansion K c Z (Z ^ τ)).blockCount : ℝ) ≤
    (expansionCutoffs K c τ).val.2 * Z ^ c.lamB := by
  have hZtwo : 2 ≤ Z := (expansionCutoffs K c τ).property.1.trans hZ
  exact (highExpansion_blockCount_bound K c Z (Z ^ τ) (by linarith)).trans
    (mul_le_mul_of_nonneg_right (expansionCutoffs_count_constant K c τ)
      (Real.rpow_nonneg (by linarith) _))

-- OBLIGATION EX-DETECTOR-WITNESSES | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_blocks (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ∀ b, BlockSource c.geometry ((highExpansion K c Z (Z ^ τ)).block b)
    c.family.B c.family.lamA (expansionCutoffs K c τ).val.2 Z := by
  intro b
  have hZtwo : 2 ≤ Z := (expansionCutoffs K c τ).property.1.trans hZ
  exact (expansionSourceCutoff_source K c τ hτ hceiling Z
    ((expansionCutoffs_source_threshold K c τ).trans hZ) b).mono
      (by linarith) (expansionCutoffs_source_constant K c τ)

-- OBLIGATION EX-TAIL | revised Proposition 6.3, §8 (pp.41–42,49–51).
-- Arbitrary external tail order, AFTER the internal height budget.
theorem expansion_tail
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound (fun Z T₁ => (highExpansion K c Z T₁).tail) := by
  exact expansionRecipeRaw_tail K c hmove

theorem expansionSource :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 2 ≤ Z₀ ∧ 0 ≤ k ∧
        ∀ Z : ℝ, Z₀ ≤ Z → ExpansionSource c.geometry (targetCharacter K c)
          (targetData K c) c.family.B c.family.lamA c.lamB k A Z (Z ^ τ) := by
  refine ⟨(expansionBudget K c).val.1, (expansionBudget K c).val.2,
    (expansionBudget K c).property.1, (expansionBudget K c).property.2, ?_⟩
  intro τ hτ hc
  refine ⟨(expansionCutoffs K c τ).val.1, (expansionCutoffs K c τ).val.2,
    (expansionCutoffs K c τ).property.1, (expansionCutoffs K c τ).property.2, ?_⟩
  intro Z hZ
  exact ⟨expansion_identity K c τ Z hτ hc hZ,
    expansion_principal K c τ Z hτ hc hZ,
    expansion_small K c τ Z hτ hc hZ,
    expansion_large K c τ Z hτ hc hZ,
    expansion_blockCount K c τ Z hτ hc hZ,
    expansion_blocks K c τ Z hτ hc hZ⟩

end HeckeSkeleton
