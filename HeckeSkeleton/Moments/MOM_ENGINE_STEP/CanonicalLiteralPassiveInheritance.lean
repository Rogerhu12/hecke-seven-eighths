import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityChild

/-!
# Original characters in the same selected passive child

The literal allocated data retain the original background and select
their slot characters through the actual allocation.  Normalization,
capacity deletion and freezing retain these characters.  The index below
composes those two selections for the already chosen child; no child,
profile, radius or arithmetic mask is replaced.

In particular, membership of the inverses of the original slot characters
passes to the output without assuming that the finite set of characters
is closed under inversion.  The only calibration identity used here is
the literal definition of its raw data.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Equality of raw data transports only the dependent slot index. -/
theorem slotCoefficient_cast {d₁ d₂ : MomentData K ω ψ} (e : d₁ = d₂)
    (i : Fin d₁.geometry.slotCount) :
    d₁.slotCoefficient i = d₂.slotCoefficient
      (Fin.cast (congrArg (fun d : MomentData K ω ψ => d.geometry.slotCount) e) i) := by
  cases e
  rfl

section LiteralData

variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "literalData" =>
  CanonicalLiteralAllocatedData.data P R W B F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
    rectangle firstSign negative

@[simp] theorem data_plainBackground (ξ : WithLp 2 (ℝ × ℝ)) :
    (literalData ξ).plainBackground = parent.plainBackground := rfl

@[simp] theorem data_theta (ξ : WithLp 2 (ℝ × ℝ)) :
    (literalData ξ).theta = parent.theta := rfl

/-- The passive allocation uses its original retained-slot embedding. -/
@[simp] theorem data_slotCoefficient (ξ : WithLp 2 (ℝ × ℝ))
    (i : Fin B.keep.card) :
    (literalData ξ).slotCoefficient i =
      parent.slotCoefficient (index (SlotRestriction.index B.keep i)) := rfl

section SelectedChild

variable {H : Type*} {sourceCount : ℕ}
variable {source : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) H sourceCount}
variable {D : source.Calibration (σ := σ) ω ψ}
variable {G : D.NormalizedCapacityData} (out : G.Child)
variable (hdata : ∀ ξ, D.data ξ = literalData ξ)

/-- The original parent index of a slot in this already selected child. -/
def selectedOriginalIndex (ξ : WithLp 2 (ℝ × ℝ))
    (i : Fin (out.frozenData ξ).geometry.slotCount) : Fin parent.geometry.slotCount :=
  index (SlotRestriction.index B.keep
    (Fin.cast
      (congrArg (fun raw : MomentData K ω ψ => raw.geometry.slotCount) (hdata ξ))
      (selectedSlotIndex
        (lengthSelection (G.normalizedData ξ) source.allocation.keep.card
          (G.normalizedData_count ξ) (Finset.univ \ out.removed)) i)))

include hdata

theorem frozen_plainBackground_eq_parent (ξ : WithLp 2 (ℝ × ℝ)) :
    (out.frozenData ξ).plainBackground = parent.plainBackground := by
  calc
    _ = (D.data ξ).plainBackground := out.frozen_plainBackground_eq ξ
    _ = (literalData ξ).plainBackground :=
      congrArg (fun raw : MomentData K ω ψ => raw.plainBackground) (hdata ξ)
    _ = parent.plainBackground := rfl

theorem frozen_theta_eq_parent (ξ : WithLp 2 (ℝ × ℝ)) :
    (out.frozenData ξ).theta = parent.theta := by
  calc
    _ = (D.data ξ).theta := out.frozen_theta_eq ξ
    _ = (literalData ξ).theta :=
      congrArg (fun raw : MomentData K ω ψ => raw.theta) (hdata ξ)
    _ = parent.theta := rfl

/-- Neither the negative Fourier side nor profile normalization inverts
the actual literal slot character. -/
theorem frozen_slotCoefficient_eq_parent (ξ : WithLp 2 (ℝ × ℝ))
    (i : Fin (out.frozenData ξ).geometry.slotCount) :
    (out.frozenData ξ).slotCoefficient i = parent.slotCoefficient
      (selectedOriginalIndex P R W B F parent oldMoving correction hcorr C p
        leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
        rectangle firstSign negative out hdata ξ i) := by
  calc
    _ = (D.data ξ).slotCoefficient (selectedSlotIndex
        (lengthSelection (G.normalizedData ξ) source.allocation.keep.card
          (G.normalizedData_count ξ) (Finset.univ \ out.removed)) i) :=
      out.frozen_slotCoefficient_eq ξ i
    _ = (literalData ξ).slotCoefficient (Fin.cast
        (congrArg (fun raw : MomentData K ω ψ => raw.geometry.slotCount) (hdata ξ))
        (selectedSlotIndex
          (lengthSelection (G.normalizedData ξ) source.allocation.keep.card
            (G.normalizedData_count ξ) (Finset.univ \ out.removed)) i)) :=
      slotCoefficient_cast (hdata ξ) _
    _ = _ := rfl

/-- Any property of the original slots passes along the same index. -/
theorem frozen_slot_property (property : HeckeCharacter K → Prop)
    (hproperty : ∀ i, property (parent.slotCoefficient i))
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin (out.frozenData ξ).geometry.slotCount) :
    property ((out.frozenData ξ).slotCoefficient i) := by
  rw [frozen_slotCoefficient_eq_parent P R W B F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
    rectangle firstSign negative out hdata ξ i]
  exact hproperty _

theorem frozen_slot_inverse_mem_parent
    (hinverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin (out.frozenData ξ).geometry.slotCount) :
    ((out.frozenData ξ).slotCoefficient i)⁻¹ ∈ parent.theta :=
  frozen_slot_property P R W B F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
    rectangle firstSign negative out hdata (fun χ => χ⁻¹ ∈ parent.theta) hinverse ξ i

theorem frozen_slot_inverse_mem_theta
    (hinverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin (out.frozenData ξ).geometry.slotCount) :
    ((out.frozenData ξ).slotCoefficient i)⁻¹ ∈ (out.frozenData ξ).theta := by
  rw [frozen_theta_eq_parent P R W B F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
    rectangle firstSign negative out hdata ξ]
  exact frozen_slot_inverse_mem_parent P R W B F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
    rectangle firstSign negative out hdata hinverse ξ i

end SelectedChild
end LiteralData

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance.data_slotCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance.frozen_plainBackground_eq_parent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance.frozen_slotCoefficient_eq_parent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance.frozen_slot_property
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveInheritance.frozen_slot_inverse_mem_theta
