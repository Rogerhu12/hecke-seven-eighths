import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCalibratedDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedSupport

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
  ext I
  rw [(W.left r).support_spec, (W.left r).support_spec, W.left_frozen]

theorem right_support_frozen (r : Bool) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (t N : ℝ) : (W.right r).support u t N = (W.right r).support 1 0 N := by
  ext I
  rw [(W.right r).support_spec, (W.right r).support_spec, W.right_frozen]

theorem slot_support_frozen (j : Fin k) (t N : ℝ) :
    (W.slot j).support t N = (W.slot j).support 0 N := by
  ext p
  rw [(W.slot j).support_spec, (W.slot j).support_spec, W.slot_frozen]

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
  rw [W.left_support_frozen]
  cases r
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

theorem right_support_subset_smooth (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.right r).support u t
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) ⊆
      W.smoothPlain₂ B := by
  rw [W.right_support_frozen]
  cases r
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

theorem fourierLeft_support_subset_smooth (r : Bool) (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.fourierLeft r sign negative ξ).support u t
        (d.scale₁ r / idealNorm K (B.plainDivisor 0)) ⊆ W.smoothPlain₁ B :=
  W.left_support_subset_smooth B r u t

theorem fourierRight_support_subset_smooth (r : Bool) (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.fourierRight r sign negative ξ).support u t
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) ⊆ W.smoothPlain₂ B :=
  W.right_support_subset_smooth B r u t

theorem fourierSlot_support_eq_smooth (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) (t : ℝ) :
    (W.fourierSlot (SlotRestriction.index B.keep i) sign negative ξ).support t
        (d.base ^ d.length (SlotRestriction.index B.keep i)) = W.smoothSlots B i :=
  W.slot_support_frozen (SlotRestriction.index B.keep i) t _

variable (A : SArithmeticData K)

def exteriorSmoothPlain₁ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.smoothPlain₁ B).filter (fun I => IsCoprime I.val A.cS)

def exteriorSmoothPlain₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.smoothPlain₂ B).filter (fun I => IsCoprime I.val A.cS)

def exteriorSmoothSlots (i : Fin B.keep.card) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (W.smoothSlots B i).filter (fun p => IsCoprime p.asIdeal A.cS)

theorem exteriorSmoothPlain₁_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ W.exteriorSmoothPlain₁ B A) : IsCoprime I.val A.cS :=
  (Finset.mem_filter.mp hI).2

theorem exteriorSmoothPlain₂_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ W.exteriorSmoothPlain₂ B A) : IsCoprime I.val A.cS :=
  (Finset.mem_filter.mp hI).2

theorem exteriorSmoothSlots_coprime (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ W.exteriorSmoothSlots B A i) :
    IsCoprime p.asIdeal A.cS := (Finset.mem_filter.mp hp).2

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
  refine ⟨?_, ?_, ?_⟩
  · intro I hI
    have hprofile := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hI).1).2
    have hmask := (mul_ne_zero_iff.mp hI).2
    have hfixed := (mask_consequences P R W B F parent oldMoving correction hcorr C p
      leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
      rectangle firstSign negative ξ u I hmask).fixed
    refine Finset.mem_filter.mpr ⟨?_, hfixed⟩
    apply W.fourierLeft_support_subset_smooth B rectangle firstSign negative ξ u (height ξ)
    exact ((W.fourierLeft rectangle firstSign negative ξ).support_spec u (height ξ) _ I).mpr
      hprofile
  · intro I hI
    have hprofile := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hI).1).2
    have hmask := (mul_ne_zero_iff.mp hI).2
    have hfixed := (mask_consequences P R W B F parent oldMoving correction hcorr C p
      leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
      rectangle firstSign negative ξ u I hmask).fixed
    refine Finset.mem_filter.mpr ⟨?_, hfixed⟩
    apply W.fourierRight_support_subset_smooth B rectangle firstSign negative ξ u (height ξ)
    exact ((W.fourierRight rectangle firstSign negative ξ).support_spec u (height ξ) _ I).mpr
      hprofile
  · intro i v hv
    have hprofile := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
    have hmask := (mul_ne_zero_iff.mp hv).2
    have hfixed := (mask_consequences P R W B F parent oldMoving correction hcorr C p
      leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
      rectangle firstSign negative ξ u
      ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ hmask).fixed
    refine Finset.mem_filter.mpr ⟨?_, hfixed⟩
    rw [← W.fourierSlot_support_eq_smooth B firstSign negative ξ i (height ξ)]
    apply ((W.fourierSlot (SlotRestriction.index B.keep i) firstSign negative ξ).support_spec
      (height ξ) _ v).mpr
    change (W.fourierSlot (SlotRestriction.index B.keep i) firstSign negative ξ).profile
      (height ξ) ((Ideal.absNorm v.asIdeal : ℝ) /
        d.base ^ (W.fourierSlot (SlotRestriction.index B.keep i) firstSign negative ξ).length)
      ≠ 0 at hprofile
    rw [W.fourierSlot_length] at hprofile
    exact hprofile

end CanonicalLiteralSmoothCarrier
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.left_support_frozen
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.fourierLeft_support_subset_smooth
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralSmoothCarrier.actual_effectiveSupports
