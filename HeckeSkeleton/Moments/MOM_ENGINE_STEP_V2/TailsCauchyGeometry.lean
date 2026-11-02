import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed geometry of the first Cauchy family

The common ideals are extracted from an actual original column pair.
Every complementary mask divisor divides both common ideals. These
facts give uniform logarithmic lengths without a nonzero coefficient
hypothesis. The rows and logarithmic kernel are the literal fields
specified in the source realization contract.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem first_common_witness (F : FirstPresentation call p) (v : F.source.CommonLabel) :
    ∃ i ∈ (F.source.block v).leftColumns F.source.columns,
      ∃ j ∈ (F.source.block v).rightColumns F.source.columns, True := by
  obtain ⟨ij, hij, hlabel⟩ := Finset.mem_image.mp v.property
  have hpair := Finset.mem_product.mp hij
  have he := (commonSupportLabel_eq_iff (F.source.ideal ij.1).val
    (F.source.ideal ij.2).val v.val.1 v.val.2
    (F.source.block v).common_support_eq).mp hlabel
  exact ⟨ij.1, Finset.mem_filter.mpr ⟨hpair.1, he.1⟩,
    ij.2, Finset.mem_filter.mpr ⟨hpair.2, he.2.1⟩, trivial⟩

theorem first_common_norms_le (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) :
    (Ideal.absNorm v.val.1 : ℝ) ≤ call.base ^ carrierColumnExponent c ∧
      (Ideal.absNorm v.val.2 : ℝ) ≤ call.base ^ carrierColumnExponent c := by
  obtain ⟨i, hi, j, hj, _⟩ := first_common_witness F v
  constructor
  · apply (tailsV2_physical_ideal_norm_le_of_dvd v.val.1 (F.source.ideal i).val
      (F.source.ideal i).property.1 ?_).trans
      (first_ideal_norm_le_all F hF input hlarge i (Finset.mem_filter.mp hi).1)
    rw [← (F.source.block v).common_left]
    exact ⟨((F.source.block v).leftResidual i).val,
      (F.source.block v).left_reconstruct F.source.columns i hi⟩
  · apply (tailsV2_physical_ideal_norm_le_of_dvd v.val.2 (F.source.ideal j).val
      (F.source.ideal j).property.1 ?_).trans
      (first_ideal_norm_le_all F hF input hlarge j (Finset.mem_filter.mp hj).1)
    rw [← (F.source.block v).common_right]
    exact ⟨((F.source.block v).rightResidual j).val,
      (F.source.block v).right_reconstruct F.source.columns j hj⟩

theorem idealLogLength_le_of_norm (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (B : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ call.base ^ B) :
    idealLogLength call.base I ≤ B := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_idealLogLength call.base call.domain.scale I hI]
  exact hN

theorem idealLogLength_mono_dvd {I J : Ideal (𝓞 K)}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ∣ J) :
    idealLogLength call.base I ≤ idealLogLength call.base J := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_idealLogLength call.base call.domain.scale I hI,
    rpow_idealLogLength call.base call.domain.scale J hJ]
  exact tailsV2_physical_ideal_norm_le_of_dvd I J hJ hIJ

theorem first_common_lengths_le (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (v : F.source.CommonLabel) :
    idealLogLength call.base v.val.1 ≤ carrierColumnExponent c ∧
      idealLogLength call.base v.val.2 ≤ carrierColumnExponent c := by
  have hnorm := first_common_norms_le F hF input hlarge v
  have hzero := commonSupportPool_nonzero F.source.columns F.source.columns
    (fun i => (F.source.ideal i).val) (fun j => (F.source.ideal j).val) v.val v.property
  exact ⟨idealLogLength_le_of_norm v.val.1 hzero.1 _ hnorm.1,
    idealLogLength_le_of_norm v.val.2 hzero.2 _ hnorm.2⟩

/-- The physical principal ideal of a mask divisor is its contraction. -/
theorem firstPhysicalDivisorIdeal_eq_under {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] (D : Finset (HeightOneSpectrum A.R)) :
    (firstPhysicalDivisorIdeal (A := A) D).val =
      (IdealMobiusMask.primeProduct D).under (𝓞 K) := by
  let delta := sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D
  have hspan : A.extendIdeal (firstPhysicalDivisorIdeal (A := A) D) =
      IdealMobiusMask.primeProduct D := by
    change A.extendIdeal (originalFrequencyIdeal (A := A) delta.val) =
      IdealMobiusMask.primeProduct D
    rw [← (originalFrequencyIdeal_generates (A := A) delta.val delta.property).2]
    exact Ideal.span_singleton_generator _
  calc
    _ = (A.extendIdeal (firstPhysicalDivisorIdeal (A := A) D)).under (𝓞 K) :=
      (SIntegerLocalization.under_map_exterior A.Sf _
        (firstPhysicalDivisorIdeal (A := A) D).property.2).symm
    _ = _ := congrArg (fun I : Ideal A.R => I.under (𝓞 K)) hspan

theorem firstPhysicalDivisorIdeal_dvd_product {A : SArithmeticData K}
    [IsPrincipalIdealRing A.R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (primes : ι → ExteriorPrime A) (multiplicity : ι → ℕ)
    (positive : ∀ i, 0 < multiplicity i) (D : Finset (HeightOneSpectrum A.R))
    (hD : D ⊆ Finset.univ.image (fun i => actualExteriorSPrime (primes i))) :
    (firstPhysicalDivisorIdeal (A := A) D).val ∣ (primePowerProduct primes multiplicity).val := by
  apply Ideal.dvd_iff_le.mpr
  rw [firstPhysicalDivisorIdeal_eq_under]
  intro a ha
  change algebraMap (𝓞 K) A.R a ∈ IdealMobiusMask.primeProduct D
  rw [IdealMobiusMask.mem_primeProduct]
  intro q hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hD hq)
  change algebraMap (𝓞 K) A.R a ∈
    (primes i).val.asIdeal.map (algebraMap (𝓞 K) A.R)
  apply Ideal.mem_map_of_mem
  have hd : (primes i).val.asIdeal ∣ (primePowerProduct primes multiplicity).val := by
    change (primes i).val.asIdeal ∣ ∏ j, (primes j).val.asIdeal ^ multiplicity j
    exact (dvd_pow_self _ (Nat.ne_of_gt (positive i))).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact (Ideal.dvd_iff_le.mp hd) ha

theorem first_key_complementary_dvd (F : FirstPresentation call p) (hF : F.Realizes)
    (key : FirstCauchyKey F) :
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val).val ∣ key.1.val.1 ∧
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val).val ∣ key.1.val.2 := by
  let b := FirstCauchyKey.block key
  have hD : key.2.1.val ⊆
      Finset.univ.image (fun j => actualExteriorSPrime (b.primes j)) := by
    have hsub := Finset.mem_powerset.mp key.2.1.property
    change key.2.1.val ⊆ F.source.mask ∪
      firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity at hsub
    rw [hF.mask, Finset.empty_union] at hsub
    exact hsub.trans (Finset.image_mono (Finset.subset_univ _))
  have hl := firstPhysicalDivisorIdeal_dvd_product b.primes b.leftMultiplicity
    b.left_positive key.2.1.val hD
  have hr := firstPhysicalDivisorIdeal_dvd_product b.primes b.rightMultiplicity
    b.right_positive key.2.1.val hD
  rw [b.common_left] at hl
  rw [b.common_right] at hr
  exact ⟨hl, hr⟩

theorem first_family_selected_length_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    idealLogLength call.base (family.source i).first.selected.val ≤ carrierColumnExponent c := by
  have h := first_common_lengths_le F hF input hlarge (family.index i).1
  rw [hf.selected i]
  split_ifs
  · exact h.2
  · exact h.1

theorem first_family_active_length_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    idealLogLength call.base
      (firstActiveRadical (family.source i).first.selected.val
        (family.source i).first.opposite.val) ≤ carrierColumnExponent c := by
  apply (idealLogLength_mono_dvd (call := call)
    (firstActiveRadical_ne_zero _ _)
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected) ?_).trans
    (first_family_selected_length_le F hF family hf input hlarge i)
  unfold firstActiveRadical
  exact support_product_dvd
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected) (Finset.filter_subset _ _)

theorem first_family_complementary_length_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    idealLogLength call.base (family.source i).first.complementary.val ≤
      carrierColumnExponent c := by
  have hdiv : (family.source i).first.complementary.val ∣
      (family.source i).first.selected.val := by
    rw [hf.complementary i, hf.selected i]
    have h := first_key_complementary_dvd F hF (family.index i)
    split_ifs
    · exact h.2
    · exact h.1
  exact (idealLogLength_mono_dvd (call := call)
    (nonZeroDivisors.coe_ne_zero (family.source i).first.complementary)
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected) hdiv).trans
      (first_family_selected_length_le F hF family hf input hlarge i)

theorem first_key_rows_card
    (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (key : FirstCauchyKey F) :
    ((FirstCauchyKey.data key).rows.card : ℝ) ≤
      2 * orbitRowConstant c * call.base ^ firstRowExponent c p := by
  unfold FirstCauchyKey.data
  split_ifs
  · have hcard := (congrArg Finset.card (hF.rightRows key.1 key.2.1)).le.trans
      Finset.card_image_le
    exact (Nat.cast_le.mpr hcard).trans
      (first_divisorRows_card F hF input hlarge key.1 key.2.1.val key.2.1.property)
  · have hcard := (congrArg Finset.card (hF.leftRows key.1 key.2.1)).le.trans
      Finset.card_image_le
    exact (Nat.cast_le.mpr hcard).trans
      (first_divisorRows_card F hF input hlarge key.1 key.2.1.val key.2.1.property)

theorem first_family_rows_card
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    ((family.source i).source.rows.card : ℝ) ≤
      2 * orbitRowConstant c * call.base ^ firstRowExponent c p := by
  have he := dependent_projection_eq
    (fun (Column : Type) (source : ActualGaussSource (Arithmetic.context c) Column) =>
      (source.rows.card : ℝ))
    (hf.column i) (hf.source i)
  rw [he]
  exact first_key_rows_card F hF input hlarge (family.index i)

theorem first_family_retained_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    (family.source i).first.retainedScale ≤ call.base ^ firstRowExponent c p := by
  rw [hf.retained i]
  exact max_le (Real.one_le_rpow call.domain.scale.le (firstRowExponent_nonneg c p))
    (first_divisorPhysicalCutoff_le F hF input hlarge (family.index i).1
      (family.index i).2.1.val (family.index i).2.1.property)

/-- The kernel is fixed before the original source, common pair, divisor
or continuous phase is chosen. -/
def firstFixedKernel (c : TargetContext K) (p : SourceParameters c) : SchwartzMap ℝ ℂ := by
  letI : IsTotallyComplex K := Arithmetic.totallyComplex c
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  let hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K (Arithmetic.data c).Sf (Arithmetic.finiteMeasure (K := K))
    (Arithmetic.localMeasures (K := K))
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
  exact CanonicalLogOrbital.fourierCLM K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) (Arithmetic.unitSubgroup c)
    (sIntegerFiniteFourierTestFunction K (Arithmetic.data c).Sf
      (Arithmetic.localMeasures (K := K)) (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
    hhat.1.continuous hhat.2 p.tilt p.tilt_pos p.tilt_half
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)

theorem first_chart_kernel_eq (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (F.source.charts v D).kernel = firstFixedKernel c p := by
  calc
    _ = (F.canonicalChart v D).kernel :=
      first_chart_project_eq F hF v D (fun _ chart => chart.kernel)
    _ = _ := rfl

theorem first_family_kernel_eq
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes) (i : Fin family.count) :
    (family.source i).firstKernel = firstFixedKernel c p := by
  rw [hf.kernel i]
  exact first_chart_kernel_eq F hF (family.index i).1 (family.index i).2.1

def firstFixedKernelMass (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  (actualFourierMeasure (firstFixedKernel c p)).real Set.univ

theorem firstFixedKernelMass_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ firstFixedKernelMass c p := ENNReal.toReal_nonneg

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_active_length_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_complementary_length_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_rows_card
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_kernel_eq
