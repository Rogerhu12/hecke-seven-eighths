import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceRawCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original second-class decoration counts

The carrier is the literal tail of `SourceClassKey`: the second mask
divisor, both original occurrence covers, the physical row class, and
both second extraction tuples.  All occurrence counts are bounded by
the original call's slot count through the cover's reconstruction
contract.  No representative row or column is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance n8ClassCountsCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace SecondSource

variable (source : SecondSource call p)
variable (LC RC : OriginalCover source.physical)

/-- The actual five decorative coordinates after the second common
pair and its mask divisor have been fixed. -/
abbrev Decoration (DE : source.CommonLabel) (D : source.stage.mask.powerset) :=
  Σ a : LC.cover.labels, Σ e : RC.cover.labels,
    Σ _label : Fin ((source.stage.charts DE D).rowLabelCount + 1),
      (LC.cover.branch a).labels (primeSupport DE.val.1) DE.val.1 ×
        (RC.cover.branch e).labels (primeSupport DE.val.1) DE.val.2

/-- This is definitionally the complete remaining `SourceClassKey`
carrier for the fixed common pair. -/
abbrev CommonDecoration (DE : source.CommonLabel) :=
  Σ D : source.stage.mask.powerset, source.Decoration LC RC DE D

theorem rowLabelCount_le_divisorCount (hsource : source.Realizes)
    (DE : source.CommonLabel) (D : source.stage.mask.powerset) :
    (source.stage.charts DE D).rowLabelCount ≤
      idealDivisorCount DE.val.1 *
        Nat.card (SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))) := by
  have hD : DE.val.1 ≠ 0 := by
    rw [← (source.block DE).common_left]
    exact (primePowerProduct (source.block DE).primes
      (source.block DE).leftMultiplicity).property.1
  have hprimes : 2 ^ (source.block DE).primeCount ≤ idealDivisorCount DE.val.1 := by
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using
      (source.block DE).originalCommonPrimeData.powerset_card_le_divisorCount hD
  exact (hsource.labelCount DE D).trans (Nat.mul_le_mul_right _ hprimes)

theorem decoration_card_le (hLC : LC.Realizes) (hRC : RC.Realizes)
    (DE : source.CommonLabel) (D : source.stage.mask.powerset) :
    Fintype.card (source.Decoration LC RC DE D) ≤
      LC.cover.labels.card * RC.cover.labels.card *
        ((source.stage.charts DE D).rowLabelCount + 1) *
        (idealDivisors DE.val.1).card ^ (c.geometry.slots + 2) *
        (idealDivisors DE.val.2).card ^ (c.geometry.slots + 2) := by
  have hD : DE.val.1 ≠ 0 := by
    rw [← (source.block DE).common_left]
    exact (primePowerProduct (source.block DE).primes
      (source.block DE).leftMultiplicity).property.1
  have hE : DE.val.2 ≠ 0 := by
    rw [← (source.block DE).common_right]
    exact (primePowerProduct (source.block DE).primes
      (source.block DE).rightMultiplicity).property.1
  simp only [Decoration, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe]
  calc
    _ ≤ ∑ _a : LC.cover.labels, ∑ _e : RC.cover.labels,
        ∑ _label : Fin ((source.stage.charts DE D).rowLabelCount + 1),
          (idealDivisors DE.val.1).card ^ (c.geometry.slots + 2) *
            (idealDivisors DE.val.2).card ^ (c.geometry.slots + 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro label _
      exact Nat.mul_le_mul
        ((LC.cover.branch a).labels_card_le_cap c.geometry.slots
          (LC.branch_slotCount_le hLC a) _ _ hD)
        ((RC.cover.branch e).labels_card_le_cap c.geometry.slots
          (RC.branch_slotCount_le hRC e) _ _ hE)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_coe, Nat.nsmul_eq_mul]
      ac_rfl

theorem commonDecoration_card_le (hsource : source.Realizes)
    (hLC : LC.Realizes) (hRC : RC.Realizes) (DE : source.CommonLabel) :
    Fintype.card (source.CommonDecoration LC RC DE) ≤
      LC.cover.labels.card * RC.cover.labels.card *
        (idealDivisorCount DE.val.1 *
          Nat.card (SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))) + 1) *
        (idealDivisors DE.val.1).card ^ (c.geometry.slots + 2) *
        (idealDivisors DE.val.2).card ^ (c.geometry.slots + 2) := by
  rw [CommonDecoration, Fintype.card_sigma]
  calc
    _ ≤ ∑ _D : source.stage.mask.powerset,
        LC.cover.labels.card * RC.cover.labels.card *
          (idealDivisorCount DE.val.1 *
            Nat.card (SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))) + 1) *
          (idealDivisors DE.val.1).card ^ (c.geometry.slots + 2) *
          (idealDivisors DE.val.2).card ^ (c.geometry.slots + 2) := by
      apply Finset.sum_le_sum
      intro D _
      exact (source.decoration_card_le LC RC hLC hRC DE D).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.add_le_add_right
            (source.rowLabelCount_le_divisorCount hsource DE D) 1))))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        hsource.mask, Finset.powerset_empty, Finset.card_singleton,
        one_nsmul]

end SecondSource

namespace SourceClassKey

variable {source : SecondSource call p}
variable {LC RC : OriginalCover source.physical}
variable (key : SourceClassKey source.stage LC.cover RC.cover)

abbrev rightSlots : ℕ :=
  ((RC.cover.branch key.2.2.2.1).branch (primeSupport key.1.val.1)
    key.1.val.2 key.2.2.2.2.2.2).keep.card

theorem leftSlots_le_original (hLC : LC.Realizes) :
    SourceClassKey.leftSlots key ≤ c.geometry.slots := by
  calc
    _ ≤ (LC.cover.branch key.2.2.1).slotCount := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ
        (((LC.cover.branch key.2.2.1).branch (primeSupport key.1.val.1)
          key.1.val.1 key.2.2.2.2.2.1).keep)
    _ ≤ _ := LC.branch_slotCount_le hLC _

theorem rightSlots_le_original (hRC : RC.Realizes) :
    SourceClassKey.rightSlots key ≤ c.geometry.slots := by
  calc
    _ ≤ (RC.cover.branch key.2.2.2.1).slotCount := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ
        (((RC.cover.branch key.2.2.2.1).branch (primeSupport key.1.val.1)
          key.1.val.2 key.2.2.2.2.2.2).keep)
    _ ≤ _ := RC.branch_slotCount_le hRC _

end SourceClassKey
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondSource.commonDecoration_card_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.leftSlots_le_original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.rightSlots_le_original
