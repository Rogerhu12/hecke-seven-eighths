import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveRadius
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocationProfiles

/-!
# The same computed radius on an active passive-allocation branch

The additional passive allocation divides the two already allocated
plain scales by its actual nonzero ideals.  A nonzero member of this
new branch supplies its own plain support witnesses.  Their scale and
clipping bounds therefore hold without asserting that the signed sum
before passive deletion was nonzero.

The resulting estimate controls the coefficient already computed by
`ComputedProfiles.passiveTable`, at the new branch's actual parameters.
The finite orders, original shape factor, and fixed final coefficient
are unchanged.  All three genuine plain divisors are retained in the
scale identities used to return to the original first extraction.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralPassiveActiveRadius

open CanonicalLiteralPassiveSource

variable {K : Type} [Field K] [NumberField K]

section QuotientScales

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (allocation : ActualColumnAllocation K k)
variable (A : SArithmeticData K)
variable (paid : FixedChildCharacters K allocation.keep.card)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M })

/-- Both divisors are the stored occurrence divisors; no norm window
or nonzero-energy hypothesis enters this identity. -/
theorem left_scale (r : Bool) (m q κ : ℝ) :
    d.base ^ (CanonicalLiteralAllocatedData.parameters (table W allocation A paid)
      (branch W allocation A M a) r m q κ).n₁ =
        d.scale₁ r / idealNorm K (allocation.plainDivisor 0 *
          (branch W allocation A M a).plainDivisor 0) := by
  rw [CanonicalLiteralAllocatedData.left_scale]
  change (d.scale₁ r / idealNorm K (allocation.plainDivisor 0)) /
    idealNorm K ((branch W allocation A M a).plainDivisor 0) = _
  rw [CanonicalLiteralProfileData.idealNorm_mul, div_div]

theorem right_scale (r : Bool) (m q κ : ℝ) :
    d.base ^ (CanonicalLiteralAllocatedData.parameters (table W allocation A paid)
      (branch W allocation A M a) r m q κ).n₂ =
        d.scale₂ r / idealNorm K (allocation.plainDivisor (Fin.succ 0) *
          (branch W allocation A M a).plainDivisor (Fin.succ 0)) := by
  rw [CanonicalLiteralAllocatedData.right_scale]
  change (d.scale₂ r / idealNorm K (allocation.plainDivisor (Fin.succ 0))) /
    idealNorm K ((branch W allocation A M a).plainDivisor (Fin.succ 0)) = _
  rw [CanonicalLiteralProfileData.idealNorm_mul, div_div]

end QuotientScales

section ActualTable

variable {k n : ℕ} (original : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {firstSupport : Finset (Ideal (𝓞 K))}
variable (first : SupportCartesianBranch original.plain₁ original.plain₂ original.slots firstSupport)
variable (beforeSecond : CanonicalLiteralRectangles.Atoms (K := K) n)
variable {secondSupport : Finset (Ideal (𝓞 K))}
variable (second : SupportCartesianBranch beforeSecond.plain₁ beforeSecond.plain₂
  beforeSecond.slots secondSupport)
variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : second.keep.card = atlas.slotCount)
variable (scalar : ℂ) (balance : Bool → ℝ)
variable (W : ((((beforeSecond.extract second).onAtlas atlas count).scale scalar)
  .balancePlain balance).ProfileData)
variable (allocation : ActualColumnAllocation K atlas.slotCount)
variable (paid : FixedChildCharacters K allocation.keep.card)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M })

local notation "actualTable" =>
  (((beforeSecond.extract second).onAtlas atlas count).scale scalar).balancePlain balance

local notation "passiveAllocation" => branch W allocation A M a
local notation "passiveTable" => table W allocation A paid
local notation "passiveProfiles" => profiles W allocation A paid

/-- The second common divisor, original allocation divisor, and new
passive divisor all remain in the exact quotient scale. -/
theorem atlas_left_scale (r : Bool) (m q κ : ℝ) :
    beforeSecond.base ^ (CanonicalLiteralAllocatedData.parameters passiveTable
      passiveAllocation r m q κ).n₁ =
        beforeSecond.scale₁ r / idealNorm K (second.plainDivisor₁ *
          (allocation.plainDivisor 0 * (passiveAllocation).plainDivisor 0)) := by
  have hbase : (actualTable).base = beforeSecond.base :=
    (beforeSecond.extract second).onAtlas_base_eq atlas count
  calc
    _ = (actualTable).base ^ (CanonicalLiteralAllocatedData.parameters passiveTable
        passiveAllocation r m q κ).n₁ := by rw [hbase]
    _ = (actualTable).scale₁ r / idealNorm K
        (allocation.plainDivisor 0 * (passiveAllocation).plainDivisor 0) :=
      left_scale W allocation A paid M a r m q κ
    _ = _ := by
      change ((beforeSecond.extract second).onAtlas atlas count).scale₁ r /
        idealNorm K (allocation.plainDivisor 0 * (passiveAllocation).plainDivisor 0) = _
      rw [(beforeSecond.extract second).onAtlas_left_scale atlas count r]
      change (beforeSecond.scale₁ r / idealNorm K second.plainDivisor₁) /
        idealNorm K (allocation.plainDivisor 0 * (passiveAllocation).plainDivisor 0) = _
      simp only [CanonicalLiteralProfileData.idealNorm_mul, div_div, mul_assoc]

theorem atlas_right_scale (r : Bool) (m q κ : ℝ) :
    beforeSecond.base ^ (CanonicalLiteralAllocatedData.parameters passiveTable
      passiveAllocation r m q κ).n₂ =
        beforeSecond.scale₂ r / idealNorm K (second.plainDivisor₂ *
          (allocation.plainDivisor (Fin.succ 0) *
            (passiveAllocation).plainDivisor (Fin.succ 0))) := by
  have hbase : (actualTable).base = beforeSecond.base :=
    (beforeSecond.extract second).onAtlas_base_eq atlas count
  calc
    _ = (actualTable).base ^ (CanonicalLiteralAllocatedData.parameters passiveTable
        passiveAllocation r m q κ).n₂ := by rw [hbase]
    _ = (actualTable).scale₂ r / idealNorm K
        (allocation.plainDivisor (Fin.succ 0) *
          (passiveAllocation).plainDivisor (Fin.succ 0)) :=
      right_scale W allocation A paid M a r m q κ
    _ = _ := by
      change ((beforeSecond.extract second).onAtlas atlas count).scale₂ r /
        idealNorm K (allocation.plainDivisor (Fin.succ 0) *
          (passiveAllocation).plainDivisor (Fin.succ 0)) = _
      rw [(beforeSecond.extract second).onAtlas_right_scale atlas count r]
      change (beforeSecond.scale₂ r / idealNorm K second.plainDivisor₂) /
        idealNorm K (allocation.plainDivisor (Fin.succ 0) *
          (passiveAllocation).plainDivisor (Fin.succ 0)) = _
      simp only [CanonicalLiteralProfileData.idealNorm_mul, div_div, mul_assoc]

variable {ω ψ : HeckeCharacter K}
variable {lo hi B : ℝ} {s : Finset (ℕ × ℕ)}
variable (T : CanonicalLiteralFullKappaInput.ComputedProfiles W (Set.Icc lo hi) s B)

/-- The nonzero witness belongs to this passive branch itself.  The
bound identity comes from the original computed profile constructor
and is preserved by the actual passive-table operation. -/
theorem coefficient_le_fixed_of_nonzero
    (r : Bool) (m q κ δ₁ δ₂ firstSign : ℝ) (negative : Bool)
    (hB : 0 ≤ B) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : original.scale₁ r * original.scale₂ r =
      original.scale₁ false * original.scale₂ false)
    (hbase : beforeSecond.base = original.base)
    (hfirst₁ : beforeSecond.scale₁ r = (original.extract first).scale₁ r)
    (hfirst₂ : beforeSecond.scale₂ r = (original.extract first).scale₂ r)
    (hbound : T.bound r = B + B *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ s *
        (1 + CanonicalLiteralBalancedSchwartz.factor original first δ₁ δ₂ r))
    (ξ : WithLp 2 (ℝ × ℝ)) (child : MomentData K ω ψ) (time : ℝ)
    (hleft : child.plainTest₁ = (passiveProfiles).fourierLeft r firstSign negative ξ)
    (hright : child.plainTest₂ = (passiveProfiles).fourierRight r firstSign negative ξ)
    (hne : pairedEnergy child
      (CanonicalLiteralAllocatedData.parameters passiveTable passiveAllocation r m q κ)
      original.base time ≠ 0) :
    (T.passiveTable allocation A paid).coefficient original.base
      (CanonicalLiteralAllocatedData.parameters passiveTable passiveAllocation r m q κ)
      isCompact_Icc (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign r ≤
        CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s := by
  let parameters := CanonicalLiteralAllocatedData.parameters passiveTable
    passiveAllocation r m q κ
  have hactual := CanonicalLiteralActiveRadius.scale_and_clipping_bounds passiveProfiles
    (T.passiveTable allocation A paid).model hlo hhi firstSign negative r ξ child parameters
    original.base time original.base_gt_one hleft hright hne
  have hscale₁ : original.base ^ parameters.n₁ =
      (original.extract first).scale₁ r / idealNorm K (second.plainDivisor₁ *
        (allocation.plainDivisor 0 * (passiveAllocation).plainDivisor 0)) := by
    simpa only [hbase, hfirst₁] using
      atlas_left_scale beforeSecond second atlas count scalar balance W allocation paid M a r m q κ
  have hscale₂ : original.base ^ parameters.n₂ =
      (original.extract first).scale₂ r / idealNorm K (second.plainDivisor₂ *
        (allocation.plainDivisor (Fin.succ 0) *
          (passiveAllocation).plainDivisor (Fin.succ 0))) := by
    simpa only [hbase, hfirst₂] using
      atlas_right_scale beforeSecond second atlas count scalar balance W allocation paid M a r m q κ
  have hl : 1 / hi ≤ (original.extract first).scale₁ r :=
    hactual.1.1.trans (hscale₁.le.trans (div_le_self
      ((original.extract first).scale₁_pos r).le (one_le_idealNorm K _)))
  have hr : 1 / hi ≤ (original.extract first).scale₂ r :=
    hactual.1.2.trans (hscale₂.le.trans (div_le_self
      ((original.extract first).scale₂_pos r).le (one_le_idealNorm K _)))
  have hpower : hi ^ (-2 : ℝ) = (1 / hi) * (1 / hi) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (zero_le_one.trans hhi), Real.rpow_two]
    simp only [pow_two, one_div, mul_inv_rev]
  have hlower : hi ^ (-2 : ℝ) ≤
      (original.extract first).scale₁ false * (original.extract first).scale₂ false := by
    rw [hpower, ← original.extract_scale_product first r hproduct]
    exact mul_le_mul hl hr (div_nonneg zero_le_one (zero_le_one.trans hhi))
      ((original.extract first).scale₁_pos r).le
  have hfactor := CanonicalLiteralBalancedSchwartz.factor_le original first δ₁ δ₂ hi r hhi
    hδlo hδhi hproduct hlower
  have hcost := CanonicalLiteralAllSideClipping.cost_le_of_factors original.base parameters
    original.base_gt_one.le hi s hactual.2.1 hactual.2.2
  have hshape : 0 ≤ CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ s :=
    CanonicalLogProfiles.shapeCoefficient_nonneg _ _ _ _ _
  have hfourier : 0 ≤ CanonicalLiteralRadiusBound.fourierCoefficient lo hi hlo firstSign s :=
    CanonicalLiteralFourierWindows.coefficient_nonneg _ _ _ _ _
  have hclip : 0 ≤ 1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s := by
    have hc := CanonicalLogProfiles.clippingCoefficient_one_le hi hhi s
    linarith
  have hcompare := CanonicalLiteralRadiusBound.combined_mono hB hshape hfourier
    (Real.sqrt_nonneg _) hfactor hcost hclip
  simpa only [CanonicalLiteralFullKappaInput.ComputedProfiles.coefficient,
    CanonicalLiteralFullKappaInput.ComputedProfiles.rawCoefficient,
    CanonicalLiteralFullKappaInput.ComputedProfiles.passiveTable_bound, hbound,
    CanonicalLiteralRadiusBound.fixedCoefficient, CanonicalLiteralRadiusBound.combined,
    CanonicalLiteralRadiusBound.fourierCoefficient] using hcompare

/-- The exact active predicate of the new source supplies a raw
witness through its own calibration. The signed source preceding
passive decomposition is never assumed to be nonzero. -/
theorem coefficient_le_fixed_of_source_active
    (r : Bool) (m q κ δ₁ δ₂ firstSign : ℝ) (negative : Bool)
    (hB : 0 ≤ B) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : original.scale₁ r * original.scale₂ r =
      original.scale₁ false * original.scale₂ false)
    (hbase : beforeSecond.base = original.base)
    (hfirst₁ : beforeSecond.scale₁ r = (original.extract first).scale₁ r)
    (hfirst₂ : beforeSecond.scale₂ r = (original.extract first).scale₂ r)
    (hbound : T.bound r = B + B *
      CanonicalLiteralRadiusBound.shapeCoefficient lo hi hlo δ₁ δ₂ s *
        (1 + CanonicalLiteralBalancedSchwartz.factor original first δ₁ δ₂ r))
    {H : Type*} {sourceSlots : ℕ} {σ : K →+* ℂ}
    (source : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) H sourceSlots)
    (D : source.Calibration (σ := σ) ω ψ)
    (hsourceBase : source.base = original.base)
    (hparameters : D.parameters =
      CanonicalLiteralAllocatedData.parameters passiveTable passiveAllocation r m q κ)
    (hleft : ∀ ξ, (D.data ξ).plainTest₁ = (passiveProfiles).fourierLeft r firstSign negative ξ)
    (hright : ∀ ξ, (D.data ξ).plainTest₂ = (passiveProfiles).fourierRight r firstSign negative ξ)
    (hactive : ¬∀ ξ, source.energy (σ := σ) ξ = 0) :
    (T.passiveTable allocation A paid).coefficient source.base D.parameters isCompact_Icc
      (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign r ≤
        CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s := by
  obtain ⟨ξ, hξ⟩ := not_forall.mp hactive
  have hraw : pairedEnergy (D.data ξ) D.parameters source.base (D.height ξ) ≠ 0 := by
    intro he
    have h := D.energy_le ξ
    rw [he, mul_zero] at h
    exact hξ (le_antisymm h (source.energy_nonneg (σ := σ) ξ))
  have hfixed := coefficient_le_fixed_of_nonzero original first beforeSecond second
    atlas count scalar balance W allocation paid M a T r m q κ δ₁ δ₂ firstSign negative
    hB hlo hhi hδlo hδhi hproduct hbase hfirst₁ hfirst₂ hbound
    ξ (D.data ξ) (D.height ξ) (hleft ξ) (hright ξ)
    (by simpa only [hparameters, hsourceBase] using hraw)
  simpa only [hsourceBase, hparameters] using hfixed

end ActualTable
end CanonicalLiteralPassiveActiveRadius
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveActiveRadius.left_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveActiveRadius.right_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveActiveRadius.atlas_left_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveActiveRadius.atlas_right_scale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveActiveRadius.coefficient_le_fixed_of_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveActiveRadius.coefficient_le_fixed_of_source_active
