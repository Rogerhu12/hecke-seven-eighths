import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOrbitFibrePackets
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform original row geometry

The original nonempty parent supplies the joint row and full-mask
budget, hence its actual working row exponent is nonnegative. Every
first physical divisor divides both original common ideals. These
facts bound the first physical row exponent by one constant before
the pool, independently of every moving label and selected generator.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem idealLogLength_mono (Z : ℝ) (hZ : 1 < Z)
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) (hd : I ∣ J) :
    idealLogLength Z I ≤ idealLogLength Z J := by
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [rpow_idealLogLength Z hZ I hI, rpow_idealLogLength Z hZ J hJ]
  exact norm_le_of_dvd hJ hd

theorem firstActiveRadical_dvd_left (I J : Ideal (𝓞 K)) (hI : I ≠ 0) :
    firstActiveRadical I J ∣ I :=
  support_product_dvd hI (Finset.filter_subset _ _)

variable {A : SArithmeticData K}
variable [IsPrincipalIdealRing A.R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical mask generator generates the literal product of its
actual localized primes. Contracting preserves exterior divisibility. -/
theorem firstPhysicalDivisor_dvd_powerProduct
    (primes : ι → ExteriorPrime A) (m n e : ι → ℕ) (he : ∀ i, 0 < e i)
    (D : Finset (HeightOneSpectrum A.R))
    (hD : D ⊆ firstPrincipalPrimeMask primes m n) :
    (firstPhysicalDivisorIdeal (A := A) D).val ∣ (primePowerProduct primes e).val := by
  have hmask : A.extendIdeal (firstPhysicalDivisorIdeal (A := A) D) =
      IdealMobiusMask.primeProduct D := by
    unfold firstPhysicalDivisorIdeal
    rw [← (originalFrequencyIdeal_generates
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property).2]
    exact Ideal.span_singleton_generator _
  have hlocal : A.extendIdeal (primePowerProduct primes e) ≤
      A.extendIdeal (firstPhysicalDivisorIdeal (A := A) D) := by
    rw [hmask, IdealMobiusMask.primeProduct_eq_iInf]
    refine le_iInf (fun q => le_iInf (fun hq => ?_))
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hD hq)
    change Ideal.map (algebraMap (𝓞 K) A.R) (primePowerProduct primes e).val ≤
      Ideal.map (algebraMap (𝓞 K) A.R) (primes i).val.asIdeal
    apply Ideal.map_mono
    apply Ideal.dvd_iff_le.mp
    change (primes i).val.asIdeal ∣ ∏ j, (primes j).val.asIdeal ^ e j
    exact (dvd_pow_self _ (he i).ne').trans
      (Finset.dvd_prod_of_mem (fun j => (primes j).val.asIdeal ^ e j) (Finset.mem_univ i))
  have hglobal := Ideal.comap_mono (f := algebraMap (𝓞 K) A.R) hlocal
  apply Ideal.dvd_iff_le.mpr
  simpa only [← Ideal.under_def, SArithmeticData.extendIdeal,
    SIntegerLocalization.under_map_exterior A.Sf
      (primePowerProduct primes e).val (primePowerProduct primes e).property.2,
    SIntegerLocalization.under_map_exterior A.Sf
      (firstPhysicalDivisorIdeal (A := A) D).val
      (firstPhysicalDivisorIdeal (A := A) D).property.2] using hglobal

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

theorem t3b_oldSupport_norm_le (call : Call c) (hactive : call.Active) :
    (Arithmetic.data c).exteriorNorm call.oldSupport ≤
      call.base ^ (call.node.parameters.m + call.node.parameters.q) := by
  obtain ⟨u, hu⟩ := hactive
  have hbudget := call.source.pairedJointBudget u hu
  have hmask := call.localizedSource.source.recipe.moving.effectiveFullSupport_norm_le
    call.localizedSource.source.recipe.remaining
  calc
    _ ≤ idealNorm K u * (Arithmetic.data c).exteriorNorm call.oldSupport :=
      le_mul_of_one_le_left ((Arithmetic.data c).exteriorNorm_pos call.oldSupport).le
        (one_le_idealNorm K u)
    _ ≤ idealNorm K u * idealNorm K
        (call.localizedSource.source.recipe.moving.fullMaskSupport
          call.localizedSource.source.recipe.remaining) :=
      mul_le_mul_of_nonneg_left hmask (idealNorm_pos K u).le
    _ ≤ _ := hbudget

theorem t3b_supportLength_le_width (call : Call c) (hactive : call.Active) :
    call.supportLength ≤ call.node.parameters.m + call.node.parameters.q := by
  change idealLogLength call.base call.oldSupport.val ≤ _
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_idealLogLength call.base call.domain.scale _ call.oldSupport.property.1]
  exact call.t3b_oldSupport_norm_le hactive

theorem t3b_working_m_nonneg (call : Call c) (hactive : call.Active) :
    0 ≤ call.workingParameters.m :=
  sub_nonneg.mpr (call.t3b_supportLength_le_width hactive)

theorem t3b_working_q_nonneg (call : Call c) : 0 ≤ call.workingParameters.q :=
  idealLogLength_nonneg call.base call.domain.scale _ call.oldSupport.property.1

theorem t3b_totalLength_le (call : Call c) :
    call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z ≤
      2 + recipeInductionSigma c / 16 := by
  have hc := call.domain.padded_core
  have hw := call.width_le
  change call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z ≤ _
  linarith

end Call

namespace FirstPresentation

theorem t3b_firstDivisor_dvd_left (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val ∣ v.val.1 := by
  have hD := Finset.mem_powerset.mp D.property
  change D.val ⊆ F.source.mask ∪
    firstPrincipalPrimeMask (F.source.block v).primes
      (F.source.block v).leftMultiplicity (F.source.block v).rightMultiplicity at hD
  rw [hF.mask, Finset.empty_union] at hD
  rw [← (F.source.block v).common_left]
  exact T3b.firstPhysicalDivisor_dvd_powerProduct
    (F.source.block v).primes (F.source.block v).leftMultiplicity
    (F.source.block v).rightMultiplicity (F.source.block v).leftMultiplicity
    (F.source.block v).left_positive D.val hD

theorem t3b_firstDivisor_dvd_right (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel) (D : ((F.source.block v).mask F.source.mask).powerset) :
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val ∣ v.val.2 := by
  have hD := Finset.mem_powerset.mp D.property
  change D.val ⊆ F.source.mask ∪
    firstPrincipalPrimeMask (F.source.block v).primes
      (F.source.block v).leftMultiplicity (F.source.block v).rightMultiplicity at hD
  rw [hF.mask, Finset.empty_union] at hD
  rw [← (F.source.block v).common_right]
  exact T3b.firstPhysicalDivisor_dvd_powerProduct
    (F.source.block v).primes (F.source.block v).leftMultiplicity
    (F.source.block v).rightMultiplicity (F.source.block v).rightMultiplicity
    (F.source.block v).right_positive D.val hD

end FirstPresentation

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem t3b_complementary_dvd_opposite (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    (family.source i).first.complementary.val ∣ (family.source i).first.opposite.val := by
  rw [hfamily.complementary i, hfamily.opposite i]
  split_ifs
  · exact F.t3b_firstDivisor_dvd_left hF (family.index i).1 (family.index i).2.1
  · exact F.t3b_firstDivisor_dvd_right hF (family.index i).1 (family.index i).2.1

theorem t3b_firstFrequency_le (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    (family.source i).firstFrequency ≤ 4 + recipeInductionSigma c / 8 := by
  let source := family.source i
  have ha := T3b.idealLogLength_mono call.base call.domain.scale
    (firstActiveRadical source.first.selected.val source.first.opposite.val)
    source.first.selected.val (firstActiveRadical_ne_zero _ _)
    (nonZeroDivisors.coe_ne_zero source.first.selected)
    (T3b.firstActiveRadical_dvd_left _ _ (nonZeroDivisors.coe_ne_zero source.first.selected))
  have hD := T3b.idealLogLength_mono call.base call.domain.scale
    source.first.complementary.val source.first.opposite.val
    (nonZeroDivisors.coe_ne_zero source.first.complementary)
    (nonZeroDivisors.coe_ne_zero source.first.opposite)
    (family.t3b_complementary_dvd_opposite hF hfamily i)
  have hm := call.t3b_working_m_nonneg hF.active
  have hA := call.t3b_totalLength_le
  unfold PhysicalSource.firstFrequency
  change 2 * (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z) -
    idealLogLength call.base source.first.selected.val -
    idealLogLength call.base source.first.opposite.val +
    idealLogLength call.base (firstActiveRadical source.first.selected.val source.first.opposite.val) +
    idealLogLength call.base source.first.complementary.val - call.workingParameters.m ≤ _
  linarith

end FirstCauchyFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.t3b_working_m_nonneg
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.t3b_firstFrequency_le
