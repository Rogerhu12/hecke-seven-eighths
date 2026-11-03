import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroInputBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original ideal bounds for the first physical mask

Every actual new-mask prime is the localization of an original common
prime. Contracting the exact principal mask ideal therefore gives a
divisor of the complete common ideal. The active radical is another
literal support subproduct. Both arguments include empty masks.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction.Source
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

section Block

variable {A : SArithmeticData K} [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {I : ι → A.Exterior} {J : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- Divisibility follows by mapping the original common ideal into
each actual mask prime, then contracting the same principal ideal. -/
private theorem physical_divisor_dvd_common
    (b : FirstCommonCharacterBlock I J DE)
    (D : Finset (HeightOneSpectrum A.R)) (hD : D ⊆ b.mask ∅) :
    (firstPhysicalDivisorIdeal (A := A) D).val ∣ DE.1 := by
  let common := primePowerProduct b.primes b.leftMultiplicity
  let divisor := firstPhysicalDivisorIdeal (A := A) D
  have hmask : D ⊆ firstPrincipalPrimeMask b.primes b.leftMultiplicity b.rightMultiplicity := by
    simpa only [FirstCommonCharacterBlock.mask, Finset.empty_union] using hD
  have hmap : A.extendIdeal common ≤ IdealMobiusMask.primeProduct D := by
    rw [IdealMobiusMask.primeProduct_eq_iInf]
    refine le_iInf (fun q => le_iInf (fun hq => ?_))
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hmask hq)
    change Ideal.map (algebraMap (𝓞 K) A.R) common.val ≤
      Ideal.map (algebraMap (𝓞 K) A.R) (LocalFiniteSums.primeIdeal (b.primes i)).val
    apply Ideal.map_mono
    apply Ideal.le_of_dvd
    change (b.primes i).val.asIdeal ∣ (primePowerProduct b.primes b.leftMultiplicity).val
    rw [b.common_left]
    exact b.originalCommonPrimeData.divides i (Finset.mem_univ i)
  have hgenerator : A.extendIdeal divisor = IdealMobiusMask.primeProduct D := by
    have hg := (originalFrequencyIdeal_generates
      (A := A) (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property).2
    change Ideal.span
        ({(sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val} : Set A.R) =
      A.extendIdeal divisor at hg
    rw [← hg]
    exact Ideal.span_singleton_generator (IdealMobiusMask.primeProduct D)
  have hext : A.extendIdeal common ≤ A.extendIdeal divisor := by
    rw [hgenerator]
    exact hmap
  have hcontract : common.val ≤ divisor.val := by
    have h := Ideal.comap_mono (f := algebraMap (𝓞 K) A.R) hext
    simpa only [← Ideal.under_def, SArithmeticData.extendIdeal,
      SIntegerLocalization.under_map_exterior A.Sf common.val common.property.2,
      SIntegerLocalization.under_map_exterior A.Sf divisor.val divisor.property.2] using h
  have hdiv : divisor.val ∣ common.val := Ideal.dvd_iff_le.mpr hcontract
  simpa only [divisor, common, b.common_left] using hdiv

end Block

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- The physical divisor remains bounded by the complete common left
ideal, independently of how its principal generator was chosen. -/
theorem first_physical_divisor_norm_le
    (F : FirstPresentation call p) (hF : F.Realizes) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    (Arithmetic.data c).exteriorNorm
        (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val) ≤
      (Ideal.absNorm v.val.1 : ℝ) := by
  have hD : D.val ⊆ (F.source.block v).mask ∅ := by
    simpa only [hF.mask] using Finset.mem_powerset.mp D.property
  have hcommon : v.val.1 ≠ 0 := by
    rw [← (F.source.block v).common_left]
    exact (primePowerProduct (F.source.block v).primes
      (F.source.block v).leftMultiplicity).property.1
  exact norm_le_of_dvd hcommon (physical_divisor_dvd_common (F.source.block v) D.val hD)

/-- The actual active radical is a subproduct of the original prime
support. It has no coefficient or profile nonvanishing premise. -/
theorem first_active_norm_le (F : FirstPresentation call p) (v : F.source.CommonLabel) :
    (Ideal.absNorm (firstActiveRadical v.val.1 v.val.2) : ℝ) ≤
      (Ideal.absNorm v.val.1 : ℝ) := by
  have hcommon : v.val.1 ≠ 0 := by
    rw [← (F.source.block v).common_left]
    exact (primePowerProduct (F.source.block v).primes
      (F.source.block v).leftMultiplicity).property.1
  apply norm_le_of_dvd hcommon
  exact support_product_dvd hcommon (Finset.filter_subset _ _)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
