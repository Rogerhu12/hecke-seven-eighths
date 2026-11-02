import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildProvider

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Residual sources on the original allocated rows

The old allocation is extracted using its exact polynomial identity.
Its computed frozen scalar is absorbed in the row weight. A residual
label then changes only the allocation and the already specified paid
characters. Every quotient scale, profile weight, surviving occurrence,
location, row and extraction factor is read from the same old source.
No new normalizer or arithmetic calibration is chosen here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type*} {k : ℕ}

variable (s : ActualAllocatedSource A EngineParameter H k)

/-- The old allocation's exact surviving coefficient, on quotient
ideals. This precedes any replacement of the full mask by the paid one. -/
def extractedCoefficient (h : H) :
    ((NonzeroIdeal K × NonzeroIdeal K) ×
      (Fin s.allocation.keep.card → HeightOneSpectrum (𝓞 K))) → ℂ :=
  ((s.characters h).restrictSlots s.allocation.keep).coefficient (σ := σ)
    (s.extractedFactor h) (s.row h).element
    (s.scale₁ / idealNorm K (s.allocation.plainDivisor 0))
    (s.scale₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
    s.base s.childLength
    (fun I => s.leftWeight h (s.allocation.plainDivisor 0 * I))
    (fun I => s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun i => s.slotWeight h (SlotRestriction.index s.allocation.keep i))

def extractedLocation (h : H) :
    ((NonzeroIdeal K × NonzeroIdeal K) ×
      (Fin s.allocation.keep.card → HeightOneSpectrum (𝓞 K))) → EngineParameter :=
  childCartesianLocation
    (fun I => s.leftLocation h (s.allocation.plainDivisor 0 * I))
    (fun I => s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun i => s.slotLocation h (SlotRestriction.index s.allocation.keep i))

/-- The old scalar and the common Fourier translation are exactly the
ones given by `ActualColumnAllocation.joint_polynomial`. -/
theorem polynomial_eq_extracted (h : H) (ξ : EngineParameter) :
    jointFourierColumn s.allocation.columns
      (rawSourceCoefficient (σ := σ) (s.characters h)
        (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
        (s.leftWeight h) (s.rightWeight h) (s.slotWeight h))
      (rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ =
      s.frozenScalar (σ := σ) h *
        jointPhase ξ (frozenSourceLocation s.allocation.keep s.allocation.witness.2
          (s.slotLocation h)) *
        jointFourierColumn s.allocation.childColumns
          (extractedCoefficient (σ := σ) s h) (extractedLocation s h) ξ :=
  s.allocation.joint_polynomial (s.characters h)
    (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
    (s.leftWeight h) (s.rightWeight h) (s.slotWeight h)
    (s.leftLocation h) (s.rightLocation h) (s.slotLocation h) ξ

/-- The frozen scalar is paid once, in `childWeight`; the common
translation disappears because its Fourier phase has norm one. -/
theorem energy_eq_extracted (ξ : EngineParameter) :
    s.energy (σ := σ) ξ =
      jointColumnEnergy s.rows s.allocation.childColumns (s.childWeight (σ := σ))
        (extractedCoefficient (σ := σ) s) (extractedLocation s) ξ :=
  s.allocation.joint_energy s.rows s.characters s.extractedFactor
    (fun h => (s.row h).element) s.scale₁ s.scale₂ s.base s.length
    s.leftWeight s.rightWeight s.slotWeight
    s.leftLocation s.rightLocation s.slotLocation s.weight ξ

/-- All residual labels share this one exact paid coefficient. -/
def paidCoefficient (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (h : H) : AllocationColumn K s.allocation.keep.card → ℂ :=
  rawSourceCoefficient (σ := σ) (characters h) (s.extractedFactor h) (s.row h).element
    (s.scale₁ / idealNorm K (s.allocation.plainDivisor 0))
    (s.scale₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
    s.base s.childLength
    (fun I => s.leftWeight h (s.allocation.plainDivisor 0 * I))
    (fun I => s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun i => s.slotWeight h (SlotRestriction.index s.allocation.keep i))

def paidLocation (h : H) : AllocationColumn K s.allocation.keep.card → EngineParameter :=
  rawSourceLocation
    (fun I => s.leftLocation h (s.allocation.plainDivisor 0 * I))
    (fun I => s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I))
    (fun i => s.slotLocation h (SlotRestriction.index s.allocation.keep i))

/-- The actual residual source is a fieldwise construction on the same
rows. Only the finite residual allocation and the prescribed paid
characters vary; no final output or calibration is an input. -/
def source (B : PassiveAllocation.Carrier K s.allocation.keep.card)
    (mask : Ideal (𝓞 K))
    (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (a : PassiveAllocation.labels B mask) :
    ActualAllocatedSource A EngineParameter H s.allocation.keep.card where
  allocation := PassiveAllocation.allocation B mask a
  rows := s.rows
  weight := s.childWeight (σ := σ)
  originalIdeal := s.originalIdeal
  frequency := s.frequency
  extractedFactor := s.extractedFactor
  normFactor := s.normFactor
  row := s.row
  characters := characters
  scale₁ := s.scale₁ / idealNorm K (s.allocation.plainDivisor 0)
  scale₂ := s.scale₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))
  base := s.base
  base_gt_one := s.base_gt_one
  length := s.childLength
  length_pos i := s.length_pos (SlotRestriction.index s.allocation.keep i)
  leftWeight h I := s.leftWeight h (s.allocation.plainDivisor 0 * I)
  rightWeight h I := s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I)
  slotWeight h i := s.slotWeight h (SlotRestriction.index s.allocation.keep i)
  leftLocation h I := s.leftLocation h (s.allocation.plainDivisor 0 * I)
  rightLocation h I := s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I)
  slotLocation h i := s.slotLocation h (SlotRestriction.index s.allocation.keep i)

@[simp] theorem source_allocation (B : PassiveAllocation.Carrier K s.allocation.keep.card)
    (mask : Ideal (𝓞 K)) (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (a : PassiveAllocation.labels B mask) :
    (source (σ := σ) s B mask characters a).allocation =
      PassiveAllocation.allocation B mask a := rfl

@[simp] theorem source_base (B : PassiveAllocation.Carrier K s.allocation.keep.card)
    (mask : Ideal (𝓞 K)) (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (a : PassiveAllocation.labels B mask) :
    (source (σ := σ) s B mask characters a).base = s.base := rfl

@[simp] theorem source_energy (B : PassiveAllocation.Carrier K s.allocation.keep.card)
    (mask : Ideal (𝓞 K)) (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (a : PassiveAllocation.labels B mask) (ξ : EngineParameter) :
    (source (σ := σ) s B mask characters a).energy (σ := σ) ξ =
      jointColumnEnergy s.rows (PassiveAllocation.columns B a.val)
        (s.childWeight (σ := σ)) (paidCoefficient (σ := σ) s characters)
        (paidLocation s) ξ := rfl

/-- Exact insertion of the residual mask on the restored paid atom. -/
theorem restored_polynomial_eq_labels
    (B : PassiveAllocation.Carrier K s.allocation.keep.card)
    (mask : Ideal (𝓞 K)) (hmask : mask ≠ 0)
    (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (h : H) (ξ : EngineParameter) :
    jointFourierColumn ((PassiveAllocation.carrierColumns B).filter
      (fun i => IsCoprime mask (PassiveAllocation.columnIdeal i)))
      (paidCoefficient (σ := σ) s characters h) (paidLocation s h) ξ =
      ∑ a : PassiveAllocation.labels B mask, PassiveAllocation.sign a.val *
        jointFourierColumn (source (σ := σ) s B mask characters a).allocation.columns
          (paidCoefficient (σ := σ) s characters h) (paidLocation s h) ξ :=
  PassiveAllocation.residual_mobius_labels B mask hmask
    (fun i => paidCoefficient (σ := σ) s characters h i * jointPhase ξ (paidLocation s h i))

/-- Finite weighted L2 triangle on the exact same rows and atoms. The
only factors outside the actual source norms are the residual signs. -/
theorem sqrt_restored_energy_le
    (B : PassiveAllocation.Carrier K s.allocation.keep.card)
    (mask : Ideal (𝓞 K)) (hmask : mask ≠ 0)
    (characters : H → FixedChildCharacters K s.allocation.keep.card)
    (ξ : EngineParameter) :
    Real.sqrt (jointColumnEnergy s.rows
      ((PassiveAllocation.carrierColumns B).filter
        (fun i => IsCoprime mask (PassiveAllocation.columnIdeal i)))
      (s.childWeight (σ := σ)) (paidCoefficient (σ := σ) s characters)
      (paidLocation s) ξ) ≤
      ∑ a : PassiveAllocation.labels B mask, ‖PassiveAllocation.sign a.val‖ *
        Real.sqrt ((source (σ := σ) s B mask characters a).energy (σ := σ) ξ) := by
  simpa only [source_energy] using
    (PassiveAllocation.sqrt_residual_energy_le B mask hmask s.rows
      (s.childWeight (σ := σ)) (paidCoefficient (σ := σ) s characters)
      (paidLocation s) ξ)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource.source
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource.energy_eq_extracted
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource.sqrt_restored_energy_le
