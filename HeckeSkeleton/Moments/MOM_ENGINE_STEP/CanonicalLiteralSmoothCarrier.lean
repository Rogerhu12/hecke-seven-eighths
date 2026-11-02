import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCalibratedDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedSupport

set_option linter.unusedSectionVars false

/-!
# One fixed smooth carrier for both original rectangles

The two plain carriers are the unions of their actual frozen profile
supports at the two quotient scales.  The slots use their original
finite supports.  These carriers are selected before the row, its time,
the Fourier parameter and the rectangle.  Filtering only by the fixed
exterior condition keeps every nonzero term of the actual child mask.

In particular no passive first-prime deletion is built into this
carrier.  Its later Moebius expansion can therefore produce nontrivial
quotient branches.  All support statements below follow from the actual
profiles and masks, without an allowed-row or support-norm premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms.ProfileData

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)

theorem left_support_frozen (r : Bool) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (t N : ℝ) : (W.left r).support u t N = (W.left r).support 1 0 N := by
  sorry

theorem right_support_frozen (r : Bool) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (t N : ℝ) : (W.right r).support u t N = (W.right r).support 1 0 N := by
  sorry

theorem slot_support_frozen (j : Fin k) (t N : ℝ) :
    (W.slot j).support t N = (W.slot j).support 0 N := by
  sorry

def smoothPlain₁ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.left false).support 1 0 (d.scale₁ false / idealNorm K (B.plainDivisor 0)) ∪
    (W.left true).support 1 0 (d.scale₁ true / idealNorm K (B.plainDivisor 0))

def smoothPlain₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.right false).support 1 0
      (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))) ∪
    (W.right true).support 1 0
      (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0)))

def smoothSlots (i : Fin B.keep.card) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (W.slot (SlotRestriction.index B.keep i)).support 0
    (d.base ^ d.length (SlotRestriction.index B.keep i))

theorem left_support_subset_smooth (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.left r).support u t (d.scale₁ r / idealNorm K (B.plainDivisor 0)) ⊆
      W.smoothPlain₁ B := by
  sorry

theorem right_support_subset_smooth (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.right r).support u t
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) ⊆
      W.smoothPlain₂ B := by
  sorry

theorem fourierLeft_support_subset_smooth (r : Bool) (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.fourierLeft r sign negative ξ).support u t
        (d.scale₁ r / idealNorm K (B.plainDivisor 0)) ⊆ W.smoothPlain₁ B := by
  sorry

theorem fourierRight_support_subset_smooth (r : Bool) (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.fourierRight r sign negative ξ).support u t
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) ⊆ W.smoothPlain₂ B := by
  sorry

theorem fourierSlot_support_eq_smooth (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) (t : ℝ) :
    (W.fourierSlot (SlotRestriction.index B.keep i) sign negative ξ).support t
        (d.base ^ d.length (SlotRestriction.index B.keep i)) = W.smoothSlots B i := by
  sorry

variable (A : SArithmeticData K)

def exteriorSmoothPlain₁ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.smoothPlain₁ B).filter (fun I => IsCoprime I.val A.cS)

def exteriorSmoothPlain₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.smoothPlain₂ B).filter (fun I => IsCoprime I.val A.cS)

def exteriorSmoothSlots (i : Fin B.keep.card) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (W.smoothSlots B i).filter (fun p => IsCoprime p.asIdeal A.cS)

theorem exteriorSmoothPlain₁_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ W.exteriorSmoothPlain₁ B A) : IsCoprime I.val A.cS := by
  sorry

theorem exteriorSmoothPlain₂_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ W.exteriorSmoothPlain₂ B A) : IsCoprime I.val A.cS := by
  sorry

theorem exteriorSmoothSlots_coprime (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ W.exteriorSmoothSlots B A i) :
    IsCoprime p.asIdeal A.cS := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData

namespace CanonicalLiteralSmoothCarrier

open CanonicalLiteralAllocatedData CanonicalLiteralAllocatedSupport

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
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

local notation "child" => data P R W B F parent oldMoving correction hcorr C p
  leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
  rectangle firstSign negative

/-- Both rectangle choices and every actual row use the same exterior
carrier.  Only the fixed S-condition is filtered; the passive deletion
has not been used to shrink this carrier. -/
theorem actual_effectiveSupports (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.scale₁ rectangle / idealNorm K (B.plainDivisor 0)) (height ξ)
        (W.exteriorSmoothPlain₁ B A) ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0))) (height ξ)
        (W.exteriorSmoothPlain₂ B A) ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          (W.exteriorSmoothSlots B A i) := by
  sorry

end CanonicalLiteralSmoothCarrier
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.left_support_frozen
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.fourierLeft_support_subset_smooth
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralSmoothCarrier.actual_effectiveSupports
