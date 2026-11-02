import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceCarrierBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstPhysicalMaskBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T2: the original finite first rows have a fixed norm exponent

The complete first-column carrier bounds the selected common ideal,
the active radical and the actual physical mask divisor. The original
retained-scale and row windows then bound every actual row. Taking the
same finite supremum and its maximum with one also covers empty rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction.Source
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum FirstZeroProof

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem log_length_le_of_norm_le
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (B : ℝ)
    (hN : (Ideal.absNorm I : ℝ) ≤ call.base ^ B) :
    idealLogLength call.base I ≤ B := by
  have hpos : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hlog := Real.log_le_log hpos hN
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

theorem first_columns_norm_le_five
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ) := by
  apply (first_column_norm_le frame input hframe p.loss hannulusZ F hF i hi).trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  have hs : recipeInductionSigma c ≤ 1 := source_sigma_le_one
  linarith [p.loss_small]

private theorem first_common_norm_le_five
    (F : FirstPresentation call p)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ))
    (v : F.source.CommonLabel) :
    (Ideal.absNorm v.val.1 : ℝ) ≤ call.base ^ (5 : ℝ) ∧
      (Ideal.absNorm v.val.2 : ℝ) ≤ call.base ^ (5 : ℝ) := by
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp v.property
  have hn := actual_common_label_norm_le (F.source.ideal ij.1).val
    (F.source.ideal ij.2).val (F.source.ideal ij.1).property.1
      (F.source.ideal ij.2).property.1
  rw [he] at hn
  exact ⟨hn.1.trans (hN ij.1 (Finset.mem_product.mp hij).1),
    hn.2.trans (hN ij.2 (Finset.mem_product.mp hij).2)⟩

/-- Only original individual ideal norms enter this frequency bound.
Both actual Cauchy sides use the same complete common-pair carrier. -/
theorem first_family_frequency_le_of_norm_box
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ))
    (i : Fin family.count) :
    (family.source i).firstFrequency ≤ 16 := by
  have hcommon := first_common_norm_le_five F hN (family.index i).1
  have hselected :
      (Ideal.absNorm (family.source i).first.selected.val : ℝ) ≤ call.base ^ (5 : ℝ) := by
    rw [hfamily.selected i]
    split_ifs
    · exact hcommon.2
    · exact hcommon.1
  have hactive : (Ideal.absNorm (firstActiveRadical
      (family.source i).first.selected.val (family.source i).first.opposite.val) : ℝ) ≤
      call.base ^ (5 : ℝ) := by
    have hdiv : firstActiveRadical (family.source i).first.selected.val
        (family.source i).first.opposite.val ∣ (family.source i).first.selected.val :=
      support_product_dvd (family.source i).first.selected.property.1 (Finset.filter_subset _ _)
    exact (norm_le_of_dvd (family.source i).first.selected.property.1 hdiv).trans hselected
  have hphysical :
      (Ideal.absNorm (family.source i).first.complementary.val : ℝ) ≤ call.base ^ (5 : ℝ) := by
    rw [hfamily.complementary i]
    exact (first_physical_divisor_norm_le F hF (family.index i).1 (family.index i).2.1).trans
      hcommon.1
  have ha := log_length_le_of_norm_le _ (firstActiveRadical_ne_zero _ _) 5 hactive
  have hd := log_length_le_of_norm_le _ (family.source i).first.complementary.property.1 5 hphysical
  have hselected0 := idealLogLength_nonneg call.base call.domain.scale
    (family.source i).first.selected.val (family.source i).first.selected.property.1
  have hopposite0 := idealLogLength_nonneg call.base call.domain.scale
    (family.source i).first.opposite.val (family.source i).first.opposite.property.1
  have hm := working_m_nonneg call hF.active
  have htotal := working_total_le call
  have hs : recipeInductionSigma c ≤ 1 := source_sigma_le_one
  unfold PhysicalSource.firstFrequency
  linarith

/-- The real original row window is used before the finite supremum.
No assertion about a transformed row or a coefficient support is needed. -/
theorem first_source_rows_norm_le_of_norm_box
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ))
    (hWindows : ∀ i, (family.source i).Windows) (i : Fin family.count)
    (h : (Arithmetic.data c).R) (hh : h ∈ (family.source i).source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤ call.base ^ (20 : ℝ) := by
  have hretained : (family.source i).first.retainedScale ≤
      call.base ^ ((family.source i).firstFrequency + 4 * p.loss) :=
    (hWindows i).retained_upper ⟨h, hh⟩
  have hexponent : (family.source i).firstFrequency + 4 * p.loss + recipeInductionSigma c ≤ 20 := by
    have hf := first_family_frequency_le_of_norm_box F hF family hfamily hN i
    have hs : recipeInductionSigma c ≤ 1 := source_sigma_le_one
    linarith [source_loss_le_one_div_sixtyfour p]
  calc
    _ ≤ (family.source i).first.retainedScale * call.base ^ recipeInductionSigma c := by
      simpa only [hfamily.tag i, OriginalNominalTag.padding] using (hWindows i).row_upper h hh
    _ ≤ call.base ^ ((family.source i).firstFrequency + 4 * p.loss) *
        call.base ^ recipeInductionSigma c :=
      mul_le_mul_of_nonneg_right hretained (Real.rpow_nonneg call.base_pos.le _)
    _ = call.base ^ ((family.source i).firstFrequency + 4 * p.loss + recipeInductionSigma c) :=
      (Real.rpow_add call.base_pos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexponent

/-- The maximum with one preserves the bound even for an empty actual
row carrier; the finite supremum is exactly the source's original one. -/
theorem first_source_rowSize_le_of_norm_box
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ))
    (hWindows : ∀ i, (family.source i).Windows) (i : Fin family.count) :
    (family.source i).rowSize ≤ call.base ^ (20 : ℝ) := by
  unfold PhysicalSource.rowSize
  apply max_le (Real.one_le_rpow call.domain.scale.le (by norm_num))
  change (family.source i).source.rows.sup (fun h =>
      (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
        ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : NNReal)) ≤
    (⟨call.base ^ (20 : ℝ), Real.rpow_nonneg call.base_pos.le _⟩ : NNReal)
  apply Finset.sup_le
  intro h hh
  exact first_source_rows_norm_le_of_norm_box F hF family hfamily hN hWindows i h hh

/-- The logarithmic size of every actual first source is uniformly
bounded before selecting the amplification pool. -/
theorem first_source_rowExponent_le_of_norm_box
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hN : ∀ i ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ))
    (hWindows : ∀ i, (family.source i).Windows) (i : Fin family.count) :
    (family.source i).rowExponent ≤ 20 := by
  have hpos : 0 < (family.source i).rowSize :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlog := Real.log_le_log hpos
    (first_source_rowSize_le_of_norm_box F hF family hfamily hN hWindows i)
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

/-- The all-column norm premise above is supplied by the original
frame and its annulus threshold, before any row is selected. -/
theorem first_source_rowExponent_le
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hWindows : ∀ i, (family.source i).Windows) (i : Fin family.count) :
    (family.source i).rowExponent ≤ 20 :=
  first_source_rowExponent_le_of_norm_box F hF family hfamily
    (first_columns_norm_le_five frame input hframe hannulusZ F hF) hWindows i

/-- Pool realization transports this same original logarithmic size;
it does not choose or assume a larger row bound. -/
theorem pool_rowExponent_le
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hWindows : ∀ i, (family.source i).Windows)
    (P : PoolPresentation family) (hP : P.Realizes) (i : Fin family.count) :
    (P.data i).rowExponent ≤ 20 := by
  rw [hP.rowExponent i]
  exact first_source_rowExponent_le frame input hframe hannulusZ F hF family hfamily hWindows i

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
