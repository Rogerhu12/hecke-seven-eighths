module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4ComputedLengths

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the actual inner allocation cannot enlarge the raw scale product

The two plain scales are divided by norms of nonzero integral ideals.
Each discarded original slot has positive length, so its scale is at
least one. The passive refinement stores precisely the surviving slots;
its own later allocation has not yet been removed from this product.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem idealNorm_one_le (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    1 ≤ idealNorm K I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun hz => nonZeroDivisors.coe_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))

private theorem prod_cast {m n : ℕ} (h : m = n) (f : Fin m → ℝ) :
    (∏ i : Fin n, f (Fin.cast h.symm i)) = ∏ i : Fin m, f i := by
  cases h
  rfl

theorem retained_rpow_product_le {k : ℕ} (keep : Finset (Fin k))
    (Z : ℝ) (hZ : 1 ≤ Z) (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i) :
    (∏ j : Fin keep.card, Z ^ length (SlotRestriction.index keep j)) ≤
      ∏ i : Fin k, Z ^ length i := by
  have he : (∏ i : Fin k, Z ^ length i) =
      (∏ i ∈ Finset.univ \ keep, Z ^ length i) *
        ∏ j : Fin keep.card, Z ^ length (SlotRestriction.index keep j) := by
    simpa only [Finset.sdiff_eq_filter, Finset.mem_univ, true_and] using
      (SlotRestriction.product_extend keep (fun _ => (PUnit.unit : PUnit.{1}))
        (fun _ => (PUnit.unit : PUnit.{1})) (fun i _ => Z ^ length i))
  have hfrozen : 1 ≤ ∏ i ∈ Finset.univ \ keep, Z ^ length i :=
    Finset.one_le_prod₀ (fun i _ => Real.one_le_rpow hZ (hlength i))
  have hremaining : 0 ≤ ∏ j : Fin keep.card,
      Z ^ length (SlotRestriction.index keep j) :=
    Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg (zero_le_one.trans hZ) _)
  rw [he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrozen hremaining

theorem canonical_sourceScaleProduct_le_before {packet : RawLeafPacket call p}
    (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input) (side : Bool)
    (a : support.labels side) (rectangle : Bool) :
    sourceScaleProduct (seed.canonicalSource input support side a rectangle) ≤
      seed.occurrences.beforePlainScale side rectangle false *
        seed.occurrences.beforePlainScale side rectangle true *
          ∏ i, call.base ^ seed.occurrences.beforeLength side i := by
  let s := seed.canonicalSource input support side a rectangle
  have hZ : 0 < call.base := zero_lt_one.trans call.domain.scale
  have horiginal (plain : Bool) : 0 < call.originalPlainScale rectangle plain := by
    unfold Call.originalPlainScale
    split_ifs <;> exact Real.rpow_pos_of_pos hZ _
  have hbefore (plain : Bool) :
      0 < seed.occurrences.beforePlainScale side rectangle plain := by
    unfold OriginalOccurrenceData.beforePlainScale RawLeafPacket.firstPlainScale
    exact div_pos (div_pos (horiginal plain) (idealNorm_pos K _)) (idealNorm_pos K _)
  have hleft : s.scale₁ ≤ seed.occurrences.beforePlainScale side rectangle false :=
    div_le_self (hbefore false).le (idealNorm_one_le _)
  have hright : s.scale₂ ≤ seed.occurrences.beforePlainScale side rectangle true :=
    div_le_self (hbefore true).le (idealNorm_one_le _)
  have hright_nonneg : 0 ≤ s.scale₂ :=
    (div_pos (hbefore true) (idealNorm_pos K _)).le
  have hslots_eq : s.base ^ s.beforeLength =
      ∏ i : Fin (seed.ordinary.originalAllocation side).keep.card,
        call.base ^ seed.occurrences.length side i := by
    change call.base ^ (∑ i : Fin (seed.ordinary.residualSlotCount side),
      call.originalLength (seed.occurrences.remainingIndex side
        (Fin.cast (seed.residual_count side).symm i))) = _
    rw [Real.rpow_sum_of_pos hZ]
    exact prod_cast (seed.residual_count side)
      (fun i => call.base ^ seed.occurrences.length side i)
  have hslots : s.base ^ s.beforeLength ≤
      ∏ i, call.base ^ seed.occurrences.beforeLength side i := by
    rw [hslots_eq]
    exact retained_rpow_product_le (seed.ordinary.originalAllocation side).keep
      call.base call.domain.scale.le (seed.occurrences.beforeLength side)
      (fun i => (call.localizedData.geometry.slots
        (seed.occurrences.secondIndex side i)).length_pos.le)
  change s.scale₁ * s.scale₂ * s.base ^ s.beforeLength ≤ _
  exact mul_le_mul (mul_le_mul hleft hright hright_nonneg (hbefore false).le) hslots
    (Real.rpow_nonneg hZ.le _) (mul_nonneg (hbefore false).le (hbefore true).le)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.retained_rpow_product_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.canonical_sourceScaleProduct_le_before
