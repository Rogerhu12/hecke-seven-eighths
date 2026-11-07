module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroInputBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroMaskSubpower
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: the actual common-prime mask and its original radius

The first source has empty old mask. Its new common-prime mask is still
retained in full and counted through the original complete common ideal.
Only the one actual left column of a nonzero pair is needed to bound
that ideal; the unused Cartesian cross columns need no sharp window.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction.Source
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

/-- A fixed subpower constant counts the literal principal common mask.
The complete common ideal, rather than an arbitrary Boolean carrier,
pays for every subset. -/
theorem first_empty_mask_card_uniform (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
    ∀ {A : SArithmeticData K} {ι κ : Type*}
      {I : ι → A.Exterior} {J : κ → A.Exterior}
      {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
      (b : FirstCommonCharacterBlock I J DE),
      (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B →
      ((b.mask ∅).powerset.card : ℝ) ≤ C * Z ^ δ := by
  obtain ⟨C, hC, hbound⟩ := original_mask_labels_subpower (K := K) B δ hB hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ A ι κ I J DE b hN
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hcard : (b.mask ∅).card ≤ b.primeCount := by
    simpa only [Finset.card_empty, zero_add] using b.mask_card_le ∅
  have hsubsets : (b.mask ∅).powerset.card ≤
      (Finset.univ : Finset (Fin b.primeCount)).powerset.card := by
    simp only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hcard
  have hreal : ((b.mask ∅).powerset.card : ℝ) ≤
      ((Finset.univ : Finset (Fin b.primeCount)).powerset.card : ℝ) := by
    exact_mod_cast hsubsets
  exact hreal.trans (hbound Z hZ Finset.univ DE.1 hD hN b.originalCommonPrimeData)

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- The actual common label is computed from this same original pair.
Its left part divides the complete original left modulus. -/
theorem first_source_common_norm_le (F : FirstPresentation call p)
    (v : FirstZeroLabel F.source.columns F.source.columns
      F.source.ideal F.source.ideal × (F.source.Column × F.source.Column))
    (hv : v ∈ firstZeroPairs F.source.columns F.source.columns
      F.source.ideal F.source.ideal) :
    (Ideal.absNorm v.1.val.1 : ℝ) ≤
      (Arithmetic.data c).exteriorNorm (F.source.ideal v.2.1) := by
  have hmem := (mem_firstZeroPairs F.source.columns F.source.columns
    F.source.ideal F.source.ideal v).mp hv
  have hnorm := (actual_common_label_norm_le
    (F.source.ideal v.2.1).val (F.source.ideal v.2.2).val
    (F.source.ideal v.2.1).property.1 (F.source.ideal v.2.2).property.1).1
  rw [hmem.2.2] at hnorm
  exact hnorm

/-- The fixed mask constant is selected before the moving call. The
physical radius is exactly the inverse working row length. -/
theorem first_source_mask_sum_uniform (c : TargetContext K)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {call : Call c} {p : SourceParameters c}
      (F : FirstPresentation call p), F.Realizes →
    ∀ v : FirstZeroLabel F.source.columns F.source.columns
      F.source.ideal F.source.ideal × (F.source.Column × F.source.Column),
      v ∈ firstZeroPairs F.source.columns F.source.columns
        F.source.ideal F.source.ideal →
      (Arithmetic.data c).exteriorNorm (F.source.ideal v.2.1) ≤ call.base ^ B →
      (∑ D ∈ ((F.source.block v.1).mask F.source.mask).powerset,
        firstZeroDivisorWeight F.source.radius D) ≤
          C * call.base ^ (call.workingParameters.m + δ) := by
  obtain ⟨C, hC, hcard⟩ := first_empty_mask_card_uniform (K := K) B δ hB hδ
  refine ⟨C, hC, ?_⟩
  intro call p F hF v hv hN
  have hcommon := (first_source_common_norm_le F v hv).trans hN
  have hc : (((F.source.block v.1).mask F.source.mask).powerset.card : ℝ) ≤
      C * call.base ^ δ := by
    rw [hF.mask]
    exact hcard call.base call.domain.scale.le (F.source.block v.1) hcommon
  calc
    _ ≤ (((F.source.block v.1).mask F.source.mask).powerset.card : ℝ) *
        F.source.radius.val⁻¹ := firstZeroDivisorSum_le_card _ _
    _ ≤ (C * call.base ^ δ) * F.source.radius.val⁻¹ :=
      mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr F.source.radius.property.le)
    _ = C * call.base ^ (call.workingParameters.m + δ) := by
      rw [first_radius_inv F hF, mul_assoc, ← Real.rpow_add call.base_pos]
      congr 2
      ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
