import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourcePoolExtraction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual raw index inside its original supported carrier

The embedding below retains the complete source-class and allocation
key.  Only the live-leaf restriction is removed; the second common pair
still comes from nonzero coefficients of the same physical source.
The first source index, its pool prime, both independent divisors and
both occurrence allocations remain in the sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance n8RawCarrierCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}

namespace SecondFamily

variable (second : SecondFamily expansion)

theorem original_columns_extract (hF : F.Realizes) (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (hsecond : second.Realizes)
    (i : Fin expansion.count) :
    ∀ j : (second.source i).physical.Column,
      j ∈ (second.source i).physical.source.columns →
      (second.source i).physical.ancestor j ∈ call.workingRaw.exteriorColumns ∧
        supportExtract
          (call.workingRaw.columnExterior ((second.source i).physical.ancestor j)).val
          (second.source i).physical.first.fullDeletion =
            (second.source i).physical.first.selected.val *
              (second.source i).physical.first.poolPower.val := by
  simpa only [hsecond.physical i] using
    expansion.original_columns_extract hF hf hexpansion i

theorem original_cover_card_le (hF : F.Realizes) (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (hsecond : second.Realizes)
    (i : Fin expansion.count) (cover : OriginalCover (second.source i).physical)
    (hcover : cover.Realizes) :
    cover.cover.labels.card ≤
      (idealDivisors ((second.source i).physical.first.selected.val *
        (second.source i).physical.first.poolPower.val)).card ^ (c.geometry.slots + 2) := by
  apply cover.labels_card_le_divisorPower hcover _
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero (second.source i).physical.first.selected)
      (second.source i).physical.first.poolPower.property.1)
  · intro j hj
    exact (second.original_columns_extract hF hf hexpansion hsecond i j hj).1
  · intro j hj
    exact (second.original_columns_extract hF hf hexpansion hsecond i j hj).2

end SecondFamily

namespace RawCovers

variable (covers : RawCovers second)

/-- The arithmetic coordinates of a complete, possibly inactive key. -/
def arithmeticKey (key : covers.Key) :
    N8Source.ArithmeticKey (K := K) expansion.count :=
  (key.1.1,
    ((second.source key.1.1).physical.first.selected.val,
      (second.source key.1.1).physical.first.opposite.val),
    (second.source key.1.1).physical.first.residualDivisor.val,
    key.1.2.1.val, key.2.1.val)

def indexWeight (key : covers.Key) : ℝ :=
  N8Source.arithmeticWeight expansion (covers.arithmeticKey key)

theorem indexWeight_nonneg (key : covers.Key) : 0 ≤ covers.indexWeight key :=
  N8Source.arithmeticWeight_nonneg expansion _

/-- All decorations over the active common pairs, before the whole-leaf
nonvanishing restriction.  This uses the original source's nonzero
column coefficients, so its frozen first divisor is still visible. -/
def supportedKeys : Finset covers.Key :=
  Finset.univ.filter (fun key =>
    0 < (second.source key.1.1).physical.outerWeight ∧
      (second.source key.1.1).physical.source.rows.Nonempty ∧
      key.1.2.1.val ∈ (second.source key.1.1).physical.activeCommon)

def supportedIndexMass : ℝ :=
  ∑ key ∈ covers.supportedKeys, covers.indexWeight key

theorem supportedIndexMass_nonneg : 0 ≤ covers.supportedIndexMass :=
  Finset.sum_nonneg (fun key _ => covers.indexWeight_nonneg key)

end RawCovers

namespace RawFamily

variable {geometry : GeometryFamily second} (raw : RawFamily geometry)

theorem originalKey_injective :
    Function.Injective (fun j : Fin raw.count => (raw.index j).val) :=
  Subtype.val_injective.comp raw.index.injective

theorem arithmeticKey_eq_originalKey (j : Fin raw.count) :
    raw.arithmeticKey j = raw.covers.arithmeticKey (raw.index j).val := rfl

theorem indexWeight_eq_originalKey (j : Fin raw.count) :
    raw.indexWeight j = raw.covers.indexWeight (raw.index j).val := rfl

theorem originalKey_supported (j : Fin raw.count) :
    (raw.index j).val ∈ raw.covers.supportedKeys :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (raw.active j).1,
    (raw.active j).2.1, (raw.active j).2.2.1⟩

theorem indexMass_eq_originalKey_image :
    raw.indexMass =
      ∑ key ∈ Finset.univ.image (fun j : Fin raw.count => (raw.index j).val),
        raw.covers.indexWeight key := by
  rw [Finset.sum_image (fun i _ j _ h => raw.originalKey_injective h)]
  rfl

/-- Enlarging to all original decorations uses only positivity and the
actual bijection supplied by the raw source contract. -/
theorem indexMass_le_supportedIndexMass :
    raw.indexMass ≤ raw.covers.supportedIndexMass := by
  rw [raw.indexMass_eq_originalKey_image]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro key hkey
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hkey
    exact raw.originalKey_supported j
  · intro key _ _
    exact raw.covers.indexWeight_nonneg key

end RawFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondFamily.original_cover_card_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.indexMass_le_supportedIndexMass
