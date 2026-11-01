import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRawWindows

/-!
# The original Fourier window of one actual rectangle

Only the two profiles selected by this side's actual rectangle enter
its normalization radius. The unused ordinary comparison rectangle
may have arbitrary central scales; its zero coefficient does not
justify charging those scales to the active rectangle.

All representatives are those constructed from the original tests.
This is the selected-rectangle version of the literal raw constructor;
the data, slots, phases, inverse test and Fourier measure are unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (allocation : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "originalData" =>
  data P R W allocation F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern sector remaining extra m q
    parent.inverseTest index rectangle firstSign negative

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) {bound : ℝ}

/-- The displayed estimates are on the computed original
representatives. `SchwartzModel.secondInput_*_seminorm_le`, its seed
bound, and its exact atlas/balance transports construct them. -/
def selectedRawWindow
    (original : RawProfileWindow rowDomain heightDomain window s parent bound)
    (hbound : 0 ≤ bound)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left rectangle) ≤ bound)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right rectangle) ≤ bound)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain window s (originalData ξ)
      (polynomialProfileRadius
        (bound * (1 + CanonicalLiteralFourierWindows.coefficient
          window hcompact hpositive firstSign s)) (s.sup Prod.snd) (s.sup Prod.snd)
        (WithLp.ofLp ξ)) := by
  have hcoefficient := CanonicalLiteralFourierWindows.coefficient_nonneg
    window hcompact hpositive firstSign s
  have hsize := CanonicalLiteralFourierWindows.bound_le_radius
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hfourier := CanonicalLiteralFourierWindows.fourier_bound
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hnonneg : 0 ≤ CanonicalLiteralFourierWindows.coefficient
      window hcompact hpositive firstSign s * (1 + ‖ξ‖) ^ (s.sup Prod.snd) :=
    mul_nonneg hcoefficient (pow_nonneg (by positivity) _)
  refine
    { inverseRep := original.inverseRep
      leftRep := fun _ _ => E.leftFourierRep hcompact hpositive firstSign negative rectangle ξ
      rightRep := fun _ _ => E.rightFourierRep hcompact hpositive firstSign negative rectangle ξ
      primeRep := fun j _ => E.slotFourierRep hcompact hpositive firstSign negative
        (SlotRestriction.index allocation.keep j) ξ
      inverse_eq := original.inverse_eq
      left_eq := fun u t y => E.leftFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      right_eq := fun u t y => E.rightFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      prime_eq := fun j t y => E.slotFourierRep_eq
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ t y
      inverse_support := original.inverse_support
      left_support := fun _ _ _ _ _ hy =>
        E.leftFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      right_support := fun _ _ _ _ _ hy =>
        E.rightFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      prime_support := fun j _ _ _ hy => E.slotFourierRep_support
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ
          (subset_tsupport _ hy)
      inverse_bound := fun u hu t ht => (original.inverse_bound u hu t ht).trans hsize
      left_bound := fun _ _ _ _ =>
        (E.leftFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left hleft hnonneg).trans hfourier)
      right_bound := fun _ _ _ _ =>
        (E.rightFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left hright hnonneg).trans hfourier)
      prime_bound := fun j _ _ =>
        (E.slotFourierRep_bound hcompact hpositive firstSign negative
          (SlotRestriction.index allocation.keep j) ξ s).trans
            ((mul_le_mul_of_nonneg_left
              (hslot (SlotRestriction.index allocation.keep j)) hnonneg).trans hfourier) }

end CanonicalLiteralAllocatedData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.selectedRawWindow
