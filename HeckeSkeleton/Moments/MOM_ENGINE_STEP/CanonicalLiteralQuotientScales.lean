import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFullKappaInput

/-!
# The actual two successive plain quotient scales

The second common extraction and the subsequent allocation divide by
two actual nonzero ideals. Their product is the single original ideal
needed in the active-profile radius estimate. The final atlas, exact
scalar removal and plain balance change neither scale. These are
identities of the source's numeric parameters, with no nonzero-energy
or final profile-bound premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

theorem onAtlas_base_eq {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    (d.onAtlas atlas count).base = d.base := by
  cases count
  rfl

theorem onAtlas_left_scale {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) (r : Bool) :
    (d.onAtlas atlas count).scale₁ r = d.scale₁ r := by
  cases count
  rfl

theorem onAtlas_right_scale {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) (r : Bool) :
    (d.onAtlas atlas count).scale₂ r = d.scale₂ r := by
  cases count
  rfl

end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralQuotientScales

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

def leftDivisor (allocation : ActualColumnAllocation K b.keep.card) :
    HeckeGeneral.Analysis.NonzeroIdeal K := b.plainDivisor₁ * allocation.plainDivisor 0

def rightDivisor (allocation : ActualColumnAllocation K b.keep.card) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  b.plainDivisor₂ * allocation.plainDivisor (Fin.succ 0)

theorem left_scale (allocation : ActualColumnAllocation K b.keep.card)
    (r : Bool) (m q κ : ℝ) :
    d.base ^ (CanonicalLiteralAllocatedData.parameters (d.extract b) allocation r m q κ).n₁ =
      d.scale₁ r / idealNorm K (leftDivisor d b allocation) := by
  rw [CanonicalLiteralAllocatedData.left_scale]
  change (d.scale₁ r / idealNorm K b.plainDivisor₁) /
    idealNorm K (allocation.plainDivisor 0) = _
  rw [leftDivisor, CanonicalLiteralProfileData.idealNorm_mul, div_div]

theorem right_scale (allocation : ActualColumnAllocation K b.keep.card)
    (r : Bool) (m q κ : ℝ) :
    d.base ^ (CanonicalLiteralAllocatedData.parameters (d.extract b) allocation r m q κ).n₂ =
      d.scale₂ r / idealNorm K (rightDivisor d b allocation) := by
  rw [CanonicalLiteralAllocatedData.right_scale]
  change (d.scale₂ r / idealNorm K b.plainDivisor₂) /
    idealNorm K (allocation.plainDivisor (Fin.succ 0)) = _
  rw [rightDivisor, CanonicalLiteralProfileData.idealNorm_mul, div_div]

variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : b.keep.card = atlas.slotCount)
variable (c : ℂ) (balance : Bool → ℝ)

local notation "actualTable" => (((d.extract b).onAtlas atlas count).scale c).balancePlain balance

/-- The statement uses precisely the post-second table stored by the
stripped literal rectangles. The combined ideal is an actual product,
so its norm is automatically at least one in the active-radius proof. -/
theorem atlas_left_scale (allocation : ActualColumnAllocation K atlas.slotCount)
    (r : Bool) (m q κ : ℝ) :
    d.base ^ (CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ).n₁ =
      d.scale₁ r / idealNorm K (b.plainDivisor₁ * allocation.plainDivisor 0) := by
  have hbase : actualTable.base = d.base := (d.extract b).onAtlas_base_eq atlas count
  calc
    _ = actualTable.base ^
        (CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ).n₁ := by
      rw [hbase]
    _ = actualTable.scale₁ r / idealNorm K (allocation.plainDivisor 0) :=
      CanonicalLiteralAllocatedData.left_scale actualTable allocation r m q κ
    _ = _ := by
      change ((d.extract b).onAtlas atlas count).scale₁ r /
        idealNorm K (allocation.plainDivisor 0) = _
      rw [(d.extract b).onAtlas_left_scale atlas count r]
      change (d.scale₁ r / idealNorm K b.plainDivisor₁) /
        idealNorm K (allocation.plainDivisor 0) = _
      rw [CanonicalLiteralProfileData.idealNorm_mul, div_div]

theorem atlas_right_scale (allocation : ActualColumnAllocation K atlas.slotCount)
    (r : Bool) (m q κ : ℝ) :
    d.base ^ (CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ).n₂ =
      d.scale₂ r / idealNorm K (b.plainDivisor₂ * allocation.plainDivisor (Fin.succ 0)) := by
  have hbase : actualTable.base = d.base := (d.extract b).onAtlas_base_eq atlas count
  calc
    _ = actualTable.base ^
        (CanonicalLiteralAllocatedData.parameters actualTable allocation r m q κ).n₂ := by
      rw [hbase]
    _ = actualTable.scale₂ r / idealNorm K (allocation.plainDivisor (Fin.succ 0)) :=
      CanonicalLiteralAllocatedData.right_scale actualTable allocation r m q κ
    _ = _ := by
      change ((d.extract b).onAtlas atlas count).scale₂ r /
        idealNorm K (allocation.plainDivisor (Fin.succ 0)) = _
      rw [(d.extract b).onAtlas_right_scale atlas count r]
      change (d.scale₂ r / idealNorm K b.plainDivisor₂) /
        idealNorm K (allocation.plainDivisor (Fin.succ 0)) = _
      rw [CanonicalLiteralProfileData.idealNorm_mul, div_div]

end CanonicalLiteralQuotientScales
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralQuotientScales.left_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralQuotientScales.right_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralQuotientScales.atlas_left_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralQuotientScales.atlas_right_scale
