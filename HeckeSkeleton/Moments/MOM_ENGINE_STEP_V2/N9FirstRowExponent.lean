import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceFirstNorms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RemainingMaskRadical

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed row exponent for the original first-Cauchy sources

The complete original mask budget makes the working plain width
nonnegative.  The actual first mask divisor is a divisor of the same
complete common ideal.  The original physical windows then put every
first-source row in one fixed power window, including empty row sets.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace N8Source

private theorem nonzeroIdeal_norm_one_le (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    1 ≤ idealNorm K I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun hz => nonZeroDivisors.coe_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))

theorem oldSupport_norm_le (call : Call c) (active : call.Active) :
    (Arithmetic.data c).exteriorNorm call.oldSupport ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
  obtain ⟨u, hu⟩ := active
  let Q := call.localizedSource.source.recipe
  have hbudget : idealNorm K u *
      idealNorm K (Q.moving.fullMaskSupport Q.remaining) ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) :=
    call.source.pairedJointBudget u hu
  have hmask : idealNorm K (Q.moving.fullMaskSupport Q.remaining) ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) :=
    (le_mul_of_one_le_left (idealNorm_pos K _).le
      (nonzeroIdeal_norm_one_le u)).trans hbudget
  exact (Q.moving.effectiveFullSupport_norm_le Q.remaining).trans hmask

theorem supportLength_le_width (call : Call c) (active : call.Active) :
    call.supportLength ≤ call.node.parameters.m + call.node.parameters.q := by
  have hlog := Real.log_le_log ((Arithmetic.data c).exteriorNorm_pos call.oldSupport)
    (oldSupport_norm_le call active)
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

theorem working_m_nonneg (call : Call c) (active : call.Active) :
    0 ≤ call.workingParameters.m :=
  sub_nonneg.mpr (supportLength_le_width call active)

/-- The physical generator of a first mask divisor generates exactly
its localized squarefree ideal.  Since the old first mask is empty,
every one of these primes divides the original complete common ideal. -/
theorem physicalMask_dvd_common
    {A : SArithmeticData K} [IsPrincipalIdealRing A.R] {ι κ : Type}
    {I : ι → A.Exterior} {J : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (block : FirstCommonCharacterBlock I J DE)
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ block.mask ∅) :
    (firstPhysicalDivisorIdeal (A := A) D).val ∣ DE.1 := by
  let whole := primePowerProduct block.primes block.leftMultiplicity
  let divisor := firstPhysicalDivisorIdeal (A := A) D
  have hmask : D ⊆ firstPrincipalPrimeMask block.primes
      block.leftMultiplicity block.rightMultiplicity := by
    simpa only [FirstCommonCharacterBlock.mask, Finset.empty_union] using hD
  have hmap : A.extendIdeal whole ≤ IdealMobiusMask.primeProduct D := by
    rw [IdealMobiusMask.primeProduct_eq_iInf]
    refine le_iInf (fun q => le_iInf (fun hq => ?_))
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hmask hq)
    change Ideal.map (algebraMap (𝓞 K) A.R) whole.val ≤
      Ideal.map (algebraMap (𝓞 K) A.R) (LocalFiniteSums.primeIdeal (block.primes i)).val
    apply Ideal.map_mono
    apply Ideal.le_of_dvd
    change (block.primes i).val.asIdeal ∣
      (primePowerProduct block.primes block.leftMultiplicity).val
    rw [block.common_left]
    exact block.originalCommonPrimeData.divides i (Finset.mem_univ i)
  have hgenerator : A.extendIdeal divisor = IdealMobiusMask.primeProduct D := by
    have hg := (originalFrequencyIdeal_generates
      (A := A) (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property).2
    change Ideal.span
        ({(sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val} : Set A.R) =
      A.extendIdeal divisor at hg
    rw [← hg]
    exact Ideal.span_singleton_generator (IdealMobiusMask.primeProduct D)
  have hext : A.extendIdeal whole ≤ A.extendIdeal divisor := by
    rw [hgenerator]
    exact hmap
  have hcontract : whole.val ≤ divisor.val := by
    have h := Ideal.comap_mono (f := algebraMap (𝓞 K) A.R) hext
    simpa only [← Ideal.under_def, SArithmeticData.extendIdeal,
      SIntegerLocalization.under_map_exterior A.Sf whole.val whole.property.2,
      SIntegerLocalization.under_map_exterior A.Sf divisor.val divisor.property.2] using h
  have hdiv : divisor.val ∣ whole.val := Ideal.dvd_iff_le.mpr hcontract
  simpa only [divisor, whole, block.common_left] using hdiv

theorem idealLogLength_le_of_norm {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (B : ℝ) (bound : (Ideal.absNorm I : ℝ) ≤ call.base ^ B) :
    idealLogLength call.base I ≤ B := by
  have hnorm : (0 : ℝ) < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hlog := Real.log_le_log hnorm bound
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

def firstRetainedExponent (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  2 * originalLengthBound c + 2 * columnExponent c + 4 * p.loss

def firstRowExponent (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  firstRetainedExponent c p + recipeInductionSigma c

theorem firstRowExponent_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ firstRowExponent c p := by
  have hL := (originalLengthBound_pos c).le
  have hC := (columnExponent_pos c).le
  have hs := (recipeInduction_budget (c := c)).1.le
  have hp := p.loss_pos.le
  dsimp only [firstRowExponent, firstRetainedExponent]
  linarith

end N8Source

namespace FirstCauchyKey

variable {F : FirstPresentation call p} (key : FirstCauchyKey F)

theorem complementary_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base) (hF : F.Realizes) :
    (Ideal.absNorm (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val).val : ℝ) ≤
      call.base ^ N8Source.columnExponent c := by
  have hmask : key.2.1.val ⊆ (FirstCauchyKey.block key).mask ∅ := by
    have h := Finset.mem_powerset.mp key.2.1.property
    simpa only [hF.mask] using h
  have hD : key.1.val.1 ≠ 0 := by
    rw [← (FirstCauchyKey.block key).common_left]
    exact (primePowerProduct (FirstCauchyKey.block key).primes
      (FirstCauchyKey.block key).leftMultiplicity).property.1
  exact (norm_le_of_dvd hD
    (N8Source.physicalMask_dvd_common (FirstCauchyKey.block key) key.2.1.val hmask)).trans
      (key.common_norm input large hF).1

end FirstCauchyKey

namespace PhysicalSource

variable (source : PhysicalSource call p)

theorem rowExponent_le_of_rows (B : ℝ) (hB : 0 ≤ B)
    (rows : ∀ h ∈ source.source.rows,
      (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤ call.base ^ B) :
    source.rowExponent ≤ B := by
  have hsup : source.source.rows.sup (fun h =>
      (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
        ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : NNReal)) ≤
      (⟨call.base ^ B, Real.rpow_nonneg call.base_pos.le _⟩ : NNReal) :=
    Finset.sup_le (fun h hh => rows h hh)
  have hsize : source.rowSize ≤ call.base ^ B :=
    max_le (Real.one_le_rpow call.domain.scale.le hB) hsup
  have hpos : 0 < source.rowSize :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlog := Real.log_le_log hpos hsize
  rw [Real.log_rpow call.base_pos] at hlog
  exact (div_le_iff₀ (Real.log_pos call.domain.scale)).mpr hlog

end PhysicalSource

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem complementary_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count) :
    (Ideal.absNorm (family.source i).first.complementary.val : ℝ) ≤
      call.base ^ N8Source.columnExponent c := by
  rw [hf.complementary i]
  exact (family.index i).complementary_norm input large hF

theorem retainedScale_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count)
    (windows : (family.source i).Windows) (hrows : (family.source i).source.rows.Nonempty) :
    (family.source i).first.retainedScale ≤ call.base ^ N8Source.firstRetainedExponent c p := by
  have hnorm := family.selected_opposite_norm input large hF hf i
  have hsel0 := nonZeroDivisors.coe_ne_zero (family.source i).first.selected
  have hopp0 := nonZeroDivisors.coe_ne_zero (family.source i).first.opposite
  have hrad : (Ideal.absNorm
      (firstActiveRadical (family.source i).first.selected.val
        (family.source i).first.opposite.val) : ℝ) ≤ call.base ^ N8Source.columnExponent c :=
    (norm_le_of_dvd hsel0
      (support_product_dvd hsel0 (Finset.filter_subset _ _))).trans hnorm.1
  have hradlog := N8Source.idealLogLength_le_of_norm
    (call := call) (firstActiveRadical_ne_zero _ _) _ hrad
  have hcomplog := N8Source.idealLogLength_le_of_norm
    (call := call) (nonZeroDivisors.coe_ne_zero (family.source i).first.complementary) _
    (family.complementary_norm input large hF hf i)
  have hsel := idealLogLength_nonneg call.base call.domain.scale _ hsel0
  have hopp := idealLogLength_nonneg call.base call.domain.scale _ hopp0
  have htotal := N8Source.working_total_le call
  have hm := N8Source.working_m_nonneg call hF.active
  apply (windows.retained_upper hrows).trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  dsimp only [N8Source.firstRetainedExponent]
  linarith

/-- The direct tag contributes its actual padding `sigma`.  Empty
source row sets are automatically handled by the maximum with one. -/
theorem rowExponent_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count)
    (windows : (family.source i).Windows) :
    (family.source i).rowExponent ≤ N8Source.firstRowExponent c p := by
  apply (family.source i).rowExponent_le_of_rows _ (N8Source.firstRowExponent_nonneg c p)
  intro h hh
  have hrow := windows.row_upper h hh
  rw [hf.tag i] at hrow
  change (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
    (family.source i).first.retainedScale * call.base ^ recipeInductionSigma c at hrow
  calc
    _ ≤ (family.source i).first.retainedScale * call.base ^ recipeInductionSigma c := hrow
    _ ≤ call.base ^ N8Source.firstRetainedExponent c p *
        call.base ^ recipeInductionSigma c :=
      mul_le_mul_of_nonneg_right (family.retainedScale_le input large hF hf i windows ⟨h, hh⟩)
        (Real.rpow_nonneg call.base_pos.le _)
    _ = _ := (Real.rpow_add call.base_pos _ _).symm

end FirstCauchyFamily

namespace N8Source

theorem first_rows_uniform_exponent (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) :
    ∃ M threshold : ℝ, 0 ≤ M ∧ 1 ≤ threshold ∧
      ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      threshold ≤ call.base → ∀ (trace : SourceTrace call p), trace.Realizes →
      ∀ i : Fin trace.cauchy.count, (trace.cauchy.source i).rowExponent ≤ M := by
  refine ⟨firstRowExponent c p, normThreshold c frame,
    firstRowExponent_nonneg c p, normThreshold_one_le c frame, ?_⟩
  intro call input hframe large trace htrace i
  have large' : normThreshold c call.frame ≤ call.base := by simpa only [hframe] using large
  exact trace.cauchy.rowExponent_le input large' htrace.first htrace.cauchy i
    (htrace.firstWindows i)

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.working_m_nonneg
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.physicalMask_dvd_common
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.first_rows_uniform_exponent
