import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileCarrier

/-!
# Literal atoms on an actual passive-deletion allocation

The quotient supports and retained occurrences are computed by the
existing `ActualColumnAllocation`. Both original rectangles use the
same frozen arithmetic scalar. Their subtraction remains intact, and
all removed Gauss scales are retained in the first plain Gauss scale.

The finite polynomial identity retains the original location composed
with the actual occurrence reconstruction. No source equality, support
budget or new normalization estimate is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support
open CanonicalLiteralProfileCarrier

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralAllocationAtoms

/-- Forgetting the nonzero proofs preserves the complete finite sum. -/
theorem sum_idealCarrier {k : ℕ}
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (f : AllocationColumn K k → ℂ) :
    (∑ i ∈ childCartesianColumns (idealCarrier S₁) (idealCarrier S₂) S, f i) =
      ∑ i ∈ childCartesianColumns S₁ S₂ S, f ((i.1.1.val, i.1.2.val), i.2) := by
  simp only [childCartesianColumns, Finset.product_eq_sprod,
    Finset.sum_product, idealCarrier]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I _
    rw [Finset.sum_image]
    · rfl
    · intro I _ J _ h
      exact Subtype.ext h
  · intro I _ J _ h
    exact Subtype.ext h

/-- The same two allocated plain factors and the original frozen slots. -/
def reconstruct {k : ℕ} (B : ActualColumnAllocation K k)
    (i : AllocationColumn K B.keep.card) : AllocationColumn K k :=
  (((B.plainDivisor 0).val * i.1.1,
      (B.plainDivisor (Fin.succ 0)).val * i.1.2),
    SlotRestriction.extend B.keep B.witness.2 i.2)

end CanonicalLiteralAllocationAtoms

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (B : ActualColumnAllocation K k)

/-- The table on the genuine quotient carrier of the allocated branch. -/
def allocate : CanonicalLiteralRectangles.Atoms (K := K) B.keep.card where
  characters := d.characters.restrictSlots B.keep
  plain₁ := idealCarrier B.childPlain₁
  plain₂ := idealCarrier B.childPlain₂
  slots := B.childSlots
  plain₁_nonzero := idealCarrier_nonzero B.childPlain₁
  plain₂_nonzero := idealCarrier_nonzero B.childPlain₂
  centered := d.centered
  scale₁ r := d.scale₁ r / idealNorm K (B.plainDivisor 0)
  scale₂ r := d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))
  scale₁_pos r := div_pos (d.scale₁_pos r) (idealNorm_pos K _)
  scale₂_pos r := div_pos (d.scale₂_pos r) (idealNorm_pos K _)
  base := d.base
  base_gt_one := d.base_gt_one
  length i := d.length (SlotRestriction.index B.keep i)
  length_pos i := d.length_pos (SlotRestriction.index B.keep i)
  leftWeight r I := d.leftWeight r (B.plainDivisor 0 * I)
  rightWeight r I := d.rightWeight r (B.plainDivisor (Fin.succ 0) * I)
  slotWeight i := d.slotWeight (SlotRestriction.index B.keep i)
  gauss₁ := d.gauss₁ * ∏ i ∈ Finset.univ \ B.keep, d.gaussSlot i
  gauss₂ := d.gauss₂
  gaussSlot i := d.gaussSlot (SlotRestriction.index B.keep i)
  gauss₁_pos := mul_pos d.gauss₁_pos (Finset.prod_pos (fun i _ => d.gaussSlot_pos i))
  gauss₂_pos := d.gauss₂_pos
  gaussSlot_pos i := d.gaussSlot_pos (SlotRestriction.index B.keep i)

theorem allocate_gaussScale :
    extraGaussScale (d.allocate B).gauss₁ (d.allocate B).gauss₂
        (d.allocate B).gaussSlot =
      extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot := by
  have hsplit : (∏ i, d.gaussSlot i) =
      (∏ i ∈ Finset.univ \ B.keep, d.gaussSlot i) *
        ∏ i, d.gaussSlot (SlotRestriction.index B.keep i) := by
    simpa only [Finset.sdiff_eq_filter, Finset.mem_univ, true_and] using
      (SlotRestriction.product_extend B.keep (fun _ => PUnit.unit)
        (fun _ => PUnit.unit) (fun i _ => d.gaussSlot i))
  change (d.gauss₁ * ∏ i ∈ Finset.univ \ B.keep, d.gaussSlot i) * d.gauss₂ *
      (∏ i, d.gaussSlot (SlotRestriction.index B.keep i)) =
    d.gauss₁ * d.gauss₂ * ∏ i, d.gaussSlot i
  rw [hsplit]
  ring

@[simp] theorem allocate_normalizer : (d.allocate B).normalizer = d.normalizer := by
  unfold normalizer
  rw [CanonicalLiteralTransforms.normalizer_eq_inv_sqrt _ _ _
      (d.allocate B).gauss₁_pos (d.allocate B).gauss₂_pos (d.allocate B).gaussSlot_pos,
    CanonicalLiteralTransforms.normalizer_eq_inv_sqrt _ _ _
      d.gauss₁_pos d.gauss₂_pos d.gaussSlot_pos,
    d.allocate_gaussScale B]

theorem allocate_rectangleLeftWeight (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.allocate B).rectangleLeftWeight r I =
      d.rectangleLeftWeight r (B.plainDivisor 0 * I) := by
  unfold rectangleLeftWeight allocate
  split_ifs <;> rfl

/-- The actual frozen arithmetic and prime-profile scalar, common to
both rectangles. The additional Gauss normalizer stays in the table. -/
def allocationScalar : ℂ :=
  d.characters.bareFrozenScalar (B.plainDivisor 0) (B.plainDivisor (Fin.succ 0))
    d.base d.length B.keep B.witness.2 d.slotWeight

theorem allocate_term (r : Bool) (i : AllocationColumn K B.keep.card)
    (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.term r (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      d.allocationScalar B * (d.allocate B).term r i := by
  have hlift₁ : sourceMomentIdeal ((B.plainDivisor 0).val * i.1.1) =
      B.plainDivisor 0 * sourceMomentIdeal i.1.1 := by
    simpa only [sourceMomentIdeal_val_of_ne_zero i.1.1 h₁] using
      sourceMomentIdeal_mul_val (B.plainDivisor 0) (sourceMomentIdeal i.1.1)
  have hlift₂ : sourceMomentIdeal ((B.plainDivisor (Fin.succ 0)).val * i.1.2) =
      B.plainDivisor (Fin.succ 0) * sourceMomentIdeal i.1.2 := by
    simpa only [sourceMomentIdeal_val_of_ne_zero i.1.2 h₂] using
      sourceMomentIdeal_mul_val (B.plainDivisor (Fin.succ 0)) (sourceMomentIdeal i.1.2)
  have hres : (d.allocate B).term r i = d.normalizer *
      (d.characters.restrictSlots B.keep).bareCoefficient
        (d.scale₁ r / idealNorm K (B.plainDivisor 0))
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
        (fun j => d.length (SlotRestriction.index B.keep j))
        (fun I => d.rectangleLeftWeight r (B.plainDivisor 0 * I))
        (fun I => d.rightWeight r (B.plainDivisor (Fin.succ 0) * I))
        (fun j => d.slotWeight (SlotRestriction.index B.keep j))
        ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) := by
    rw [term, d.allocate_normalizer B,
      funext (d.allocate_rectangleLeftWeight B r)]
    rfl
  rw [hres]
  change d.normalizer * d.characters.bareCoefficient
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight
    ((sourceMomentIdeal ((B.plainDivisor 0).val * i.1.1),
      sourceMomentIdeal ((B.plainDivisor (Fin.succ 0)).val * i.1.2)),
      SlotRestriction.extend B.keep B.witness.2 i.2) = _
  rw [hlift₁, hlift₂, d.characters.bareCoefficient_extract
    (B.plainDivisor 0) (B.plainDivisor (Fin.succ 0))
    (d.scale₁ r) (d.scale₂ r) d.base d.length B.keep B.witness.2
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight]
  unfold allocationScalar
  ring

/-- The centered subtraction is preserved before taking any norm. -/
theorem allocate_whole (i : AllocationColumn K B.keep.card)
    (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.whole (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      d.allocationScalar B * (d.allocate B).whole i := by
  unfold whole
  rw [d.allocate_term B false i h₁ h₂, d.allocate_term B true i h₁ h₂]
  ring

/-- Exact transport of the actual allocated polynomial. The location
is composed with reconstruction, including every frozen occurrence. -/
theorem allocate_polynomial {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (point : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn B.columns d.whole point ξ =
      d.allocationScalar B *
        jointFourierColumn
          (childCartesianColumns (d.allocate B).plain₁ (d.allocate B).plain₂
            (d.allocate B).slots)
          (d.allocate B).whole
          (fun i => point (CanonicalLiteralAllocationAtoms.reconstruct B i)) ξ := by
  unfold jointFourierColumn
  rw [show B.columns = WholeAllocation.pairedAllocatedColumns B.divisor B.selection
      B.plain₁ B.plain₂ B.slots id id HeightOneSpectrum.asIdeal from rfl,
    actual_allocated_polynomial_nonzero_subsupport B.divisor B.selection
      B.plain₁ B.plain₂ B.slots B.plain₁_nonzero B.plain₂_nonzero B.witness B.witness_mem]
  change _ = d.allocationScalar B *
    ∑ i ∈ childCartesianColumns (idealCarrier B.childPlain₁) (idealCarrier B.childPlain₂)
      B.childSlots, (d.allocate B).whole i *
        jointPhase ξ (point (CanonicalLiteralAllocationAtoms.reconstruct B i))
  rw [CanonicalLiteralAllocationAtoms.sum_idealCarrier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change d.whole (CanonicalLiteralAllocationAtoms.reconstruct B
      ((i.1.1.val, i.1.2.val), i.2)) *
        jointPhase ξ (point (CanonicalLiteralAllocationAtoms.reconstruct B
          ((i.1.1.val, i.1.2.val), i.2))) = _
  rw [d.allocate_whole B ((i.1.1.val, i.1.2.val), i.2)
    (nonZeroDivisors.coe_ne_zero i.1.1) (nonZeroDivisors.coe_ne_zero i.1.2)]
  ring

section Frequency

variable {A : SArithmeticData K} {σ : K →+* ℂ}

/-- The original actual frequency is evaluated at every occurrence. -/
def frequencyTerm (g h : A.R) (r : Bool) (i : AllocationColumn K k) : ℂ :=
  d.normalizer * rawSourceCoefficient (σ := σ) d.characters g h
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i

def frequencyWhole (g h : A.R) (i : AllocationColumn K k) : ℂ :=
  d.frequencyTerm (σ := σ) g h false i - d.frequencyTerm (σ := σ) g h true i

/-- The actual frozen residue belongs to the original allocation
scalar. It is never replaced by a unit or another chosen character. -/
theorem allocate_frequency_term (g h : A.R) (r : Bool)
    (i : AllocationColumn K B.keep.card) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.frequencyTerm (σ := σ) g h r (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        (d.allocate B).frequencyTerm (σ := σ) g h r i := by
  have hlift₁ : sourceMomentIdeal ((B.plainDivisor 0).val * i.1.1) =
      B.plainDivisor 0 * sourceMomentIdeal i.1.1 := by
    simpa only [sourceMomentIdeal_val_of_ne_zero i.1.1 h₁] using
      sourceMomentIdeal_mul_val (B.plainDivisor 0) (sourceMomentIdeal i.1.1)
  have hlift₂ : sourceMomentIdeal ((B.plainDivisor (Fin.succ 0)).val * i.1.2) =
      B.plainDivisor (Fin.succ 0) * sourceMomentIdeal i.1.2 := by
    simpa only [sourceMomentIdeal_val_of_ne_zero i.1.2 h₂] using
      sourceMomentIdeal_mul_val (B.plainDivisor (Fin.succ 0)) (sourceMomentIdeal i.1.2)
  have hres : (d.allocate B).frequencyTerm (σ := σ) g h r i = d.normalizer *
      (d.characters.restrictSlots B.keep).coefficient (σ := σ) g h
        (d.scale₁ r / idealNorm K (B.plainDivisor 0))
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
        (fun j => d.length (SlotRestriction.index B.keep j))
        (fun I => d.rectangleLeftWeight r (B.plainDivisor 0 * I))
        (fun I => d.rightWeight r (B.plainDivisor (Fin.succ 0) * I))
        (fun j => d.slotWeight (SlotRestriction.index B.keep j))
        ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2) := by
    rw [frequencyTerm, d.allocate_normalizer B,
      funext (d.allocate_rectangleLeftWeight B r)]
    rfl
  rw [hres]
  change d.normalizer * d.characters.coefficient (σ := σ) g h
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight
    ((sourceMomentIdeal ((B.plainDivisor 0).val * i.1.1),
      sourceMomentIdeal ((B.plainDivisor (Fin.succ 0)).val * i.1.2)),
      SlotRestriction.extend B.keep B.witness.2 i.2) = _
  rw [hlift₁, hlift₂, d.characters.coefficient_extract (σ := σ) g h
    (B.plainDivisor 0) (B.plainDivisor (Fin.succ 0))
    (d.scale₁ r) (d.scale₂ r) d.base d.length B.keep B.witness.2
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight]
  unfold ActualColumnAllocation.scalar
  ring

theorem allocate_frequency_whole (g h : A.R)
    (i : AllocationColumn K B.keep.card) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.frequencyWhole (σ := σ) g h (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        (d.allocate B).frequencyWhole (σ := σ) g h i := by
  unfold frequencyWhole
  rw [d.allocate_frequency_term B g h false i h₁ h₂,
    d.allocate_frequency_term B g h true i h₁ h₂]
  ring

/-- The exact allocated polynomial with the same complete actual
frequency, both original rectangles, and one original normalizer. -/
theorem allocate_frequency_polynomial {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g h : A.R) (point : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn B.columns (d.frequencyWhole (σ := σ) g h) point ξ =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        jointFourierColumn
          (childCartesianColumns (d.allocate B).plain₁ (d.allocate B).plain₂
            (d.allocate B).slots)
          ((d.allocate B).frequencyWhole (σ := σ) g h)
          (fun i => point (CanonicalLiteralAllocationAtoms.reconstruct B i)) ξ := by
  unfold jointFourierColumn
  rw [show B.columns = WholeAllocation.pairedAllocatedColumns B.divisor B.selection
      B.plain₁ B.plain₂ B.slots id id HeightOneSpectrum.asIdeal from rfl,
    actual_allocated_polynomial_nonzero_subsupport B.divisor B.selection
      B.plain₁ B.plain₂ B.slots B.plain₁_nonzero B.plain₂_nonzero B.witness B.witness_mem]
  change _ = B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
    ∑ i ∈ childCartesianColumns (idealCarrier B.childPlain₁) (idealCarrier B.childPlain₂)
      B.childSlots, (d.allocate B).frequencyWhole (σ := σ) g h i *
        jointPhase ξ (point (CanonicalLiteralAllocationAtoms.reconstruct B i))
  rw [CanonicalLiteralAllocationAtoms.sum_idealCarrier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change d.frequencyWhole (σ := σ) g h (CanonicalLiteralAllocationAtoms.reconstruct B
      ((i.1.1.val, i.1.2.val), i.2)) *
        jointPhase ξ (point (CanonicalLiteralAllocationAtoms.reconstruct B
          ((i.1.1.val, i.1.2.val), i.2))) = _
  rw [d.allocate_frequency_whole B g h ((i.1.1.val, i.1.2.val), i.2)
    (nonZeroDivisors.coe_ne_zero i.1.1) (nonZeroDivisors.coe_ne_zero i.1.2)]
  ring

end Frequency

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- Quotient scales retain the same frozen smooth functions. Only
their ideal arguments and surviving occurrence indices are changed. -/
def allocate : (d.allocate B).ProfileData where
  left := W.left
  right := W.right
  slot i := W.slot (SlotRestriction.index B.keep i)
  slot_length i := W.slot_length (SlotRestriction.index B.keep i)
  left_positive := W.left_positive
  right_positive := W.right_positive
  slot_positive i := W.slot_positive (SlotRestriction.index B.keep i)
  left_frozen := W.left_frozen
  right_frozen := W.right_frozen
  slot_frozen i := W.slot_frozen (SlotRestriction.index B.keep i)
  left_eval r u t I := by
    change (W.left r).profile u t
      (idealNorm K I / (d.scale₁ r / idealNorm K (B.plainDivisor 0))) = _
    rw [CanonicalLiteralProfileData.quotient_argument, W.left_eval,
      d.allocate_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t
      (idealNorm K I / (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0)))) = _
    rw [CanonicalLiteralProfileData.quotient_argument, W.right_eval] <;> rfl
  slot_eval i t p := W.slot_eval (SlotRestriction.index B.keep i) t p

@[simp] theorem allocate_left (r : Bool) : (W.allocate B).left r = W.left r := rfl
@[simp] theorem allocate_right (r : Bool) : (W.allocate B).right r = W.right r := rfl
@[simp] theorem allocate_slot (i : Fin B.keep.card) :
    (W.allocate B).slot i = W.slot (SlotRestriction.index B.keep i) := rfl

end ProfileData
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.allocate_gaussScale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.allocate_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.allocate_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.allocate_frequency_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.allocate
