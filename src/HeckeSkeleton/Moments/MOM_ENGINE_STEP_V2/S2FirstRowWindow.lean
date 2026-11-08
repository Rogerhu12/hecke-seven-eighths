module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S2FirstFamilyData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Physical first rows retain their actual orbital norm bound

Both Cauchy sides use the original fixed-divisor row set. Negating its
chosen representative preserves the original principal ideal. The direct
padding is paid only after the sharper physical cutoff inequality.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

theorem originalFrequencyIdeal_neg {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] (h : A.R) :
    originalFrequencyIdeal (-h) = originalFrequencyIdeal h := by
  by_cases hh : h = 0
  · simp only [hh, neg_zero]
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  change A.extendIdeal (originalFrequencyIdeal (-h)) =
    A.extendIdeal (originalFrequencyIdeal h)
  rw [← (originalFrequencyIdeal_generates (-h) (neg_ne_zero.mpr hh)).2,
    ← (originalFrequencyIdeal_generates h hh).2]
  simp

theorem originalFrequencyIdeal_out_norm {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] {Γ : Subgroup A.U}
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    A.exteriorNorm (originalFrequencyIdeal q.out.val) =
      (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q).val := by
  rw [originalFrequencyIdeal, dif_pos q.out.property]
  have hnorm := generates_sIntegerElementNorm
    (ProbeOrbitNormSum.principalExterior A q.out) q.out.val
    (ProbeOrbitNormSum.principalExterior_generates A q.out)
  exact hnorm.symm.trans (congrArg Subtype.val
    (sIntegerOrbitNorm_out K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ q))

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

theorem source_row_norm_le_cutoff (hF : F.Realizes)
    (key : FirstCauchyKey F) (N : F.source.Normalization)
    (h : (Arithmetic.data c).R) (hh : h ∈ (source key N).source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      (F.source.source key.1).divisorPhysicalCutoff key.2.1.val := by
  have hh' : h ∈ (FirstCauchyKey.data key).rows := hh
  by_cases hs : FirstCauchyKey.side key = true
  · simp only [FirstCauchyKey.data, hs, if_true] at hh'
    rw [hF.rightRows key.1 key.2.1] at hh'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh'
    rw [originalFrequencyIdeal_neg, originalFrequencyIdeal_out_norm]
    exact ((F.source.source key.1).mem_divisorRows key.2.1.val q).mp hq
  · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false] at hh'
    rw [hF.leftRows key.1 key.2.1] at hh'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hh'
    rw [originalFrequencyIdeal_out_norm]
    exact ((F.source.source key.1).mem_divisorRows key.2.1.val q).mp hq

theorem source_cutoff_one_of_nonempty (hF : F.Realizes)
    (key : FirstCauchyKey F) (N : F.source.Normalization)
    (hne : (source key N).source.rows.Nonempty) :
    1 ≤ (F.source.source key.1).divisorPhysicalCutoff key.2.1.val := by
  obtain ⟨h, hh⟩ := hne
  have hh' : h ∈ (FirstCauchyKey.data key).rows := hh
  by_cases hs : FirstCauchyKey.side key = true
  · simp only [FirstCauchyKey.data, hs, if_true] at hh'
    rw [hF.rightRows key.1 key.2.1] at hh'
    obtain ⟨q, hq, _⟩ := Finset.mem_image.mp hh'
    exact (one_le_sIntegerOrbitNorm q).trans
      (((F.source.source key.1).mem_divisorRows key.2.1.val q).mp hq)
  · simp only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false] at hh'
    rw [hF.leftRows key.1 key.2.1] at hh'
    obtain ⟨q, hq, _⟩ := Finset.mem_image.mp hh'
    exact (one_le_sIntegerOrbitNorm q).trans
      (((F.source.source key.1).mem_divisorRows key.2.1.val q).mp hq)

theorem source_retained_eq_cutoff (hF : F.Realizes)
    (key : FirstCauchyKey F) (N : F.source.Normalization)
    (hne : (source key N).source.rows.Nonempty) :
    (source key N).first.retainedScale =
      (F.source.source key.1).divisorPhysicalCutoff key.2.1.val :=
  max_eq_right (source_cutoff_one_of_nonempty hF key N hne)

theorem source_row_upper (hF : F.Realizes)
    (key : FirstCauchyKey F) (N : F.source.Normalization)
    (h : (Arithmetic.data c).R) (hh : h ∈ (source key N).source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      (source key N).first.retainedScale * call.base ^
        ((source key N).first.tag.padding (recipeInductionSigma c)) := by
  have hstep : 0 ≤ recipeInductionSigma c :=
    (recipeInduction_budget (c := c)).1.le
  have hpow : 1 ≤ call.base ^ recipeInductionSigma c :=
    Real.one_le_rpow call.domain.scale.le hstep
  have hret : 0 ≤ (source key N).first.retainedScale :=
    (source key N).first.retainedScale_pos.le
  calc
    _ ≤ (F.source.source key.1).divisorPhysicalCutoff key.2.1.val :=
      source_row_norm_le_cutoff hF key N h hh
    _ ≤ (source key N).first.retainedScale := le_max_right _ _
    _ ≤ (source key N).first.retainedScale * call.base ^
        ((source key N).first.tag.padding (recipeInductionSigma c)) :=
      le_mul_of_one_le_right hret hpow

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.source_row_upper
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.source_retained_eq_cutoff
