import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimeSupport

/-!
# The original inverse test on every actual child row

`NormProfileRecipe` controls the two plain tests, not the inverse test.
We therefore do not claim that an arbitrary original inverse profile
is independent of its row. The paired source does not use that test.
Before its calibration and normalized children are chosen, its unused
inverse test is fixed to the original test at the same original row
and time that supplied the literal profiles.

The resulting raw window is proved on all rows and all heights from
that one original representative and the computed Fourier profiles.
No bound on a newly generated row, profile family, or child is assumed.
All clipping and radius constructors can consume this returned window
without any further change of data.
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

local notation "allocated" =>
  data P R W allocation F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern sector remaining extra m q

/-- The original paired polynomial and row enumeration are independent
of this unused test. This equality precedes all normalization choices. -/
theorem data_pairedEnergy_inverse (inverse₁ inverse₂ : IdealTest K)
    (a : RealParameters) (Z t : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    pairedEnergy (allocated inverse₁ index rectangle firstSign negative ξ) a Z t =
      pairedEnergy (allocated inverse₂ index rectangle firstSign negative ξ) a Z t := rfl

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights window : Set ℝ}
variable {originalOrders : Finset (ℕ × ℕ)} {originalBound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights window originalOrders
  parent originalBound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) (horders : s ⊆ originalOrders)
variable {bound : ℝ} (hbound : 0 ≤ bound) (horiginalBound : originalBound ≤ bound)
variable (hleft : (CanonicalLogProfiles.sourceOrders s).sup
  (schwartzSeminormFamily ℂ ℝ ℂ) (E.left rectangle) ≤ bound)
variable (hright : (CanonicalLogProfiles.sourceOrders s).sup
  (schwartzSeminormFamily ℂ ℝ ℂ) (E.right rectangle) ≤ bound)
variable (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
  (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)

local notation "frozenInverse" =>
  CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time

/-- The same literal Fourier profiles, with the original inverse test
fixed before constructing the actual calibration. The returned domain
is all rows and all heights, including height zero. -/
def frozenInverseRawWindow (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow Set.univ Set.univ window s
      (allocated frozenInverse index rectangle firstSign negative ξ)
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
  have hinverse : s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (original.inverseRep reference time) ≤ bound := by
    have hmono : s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.inverseRep reference time) ≤
        originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (original.inverseRep reference time) :=
      Seminorm.finset_sup_apply_le (apply_nonneg _ _)
        (fun j hj => Seminorm.le_finset_sup_apply (horders hj))
    exact hmono.trans
      ((original.inverse_bound reference hreference time htime).trans horiginalBound)
  refine
    { inverseRep := fun _ _ => original.inverseRep reference time
      leftRep := fun _ _ => E.leftFourierRep hcompact hpositive firstSign negative rectangle ξ
      rightRep := fun _ _ => E.rightFourierRep hcompact hpositive firstSign negative rectangle ξ
      primeRep := fun j _ => E.slotFourierRep hcompact hpositive firstSign negative
        (SlotRestriction.index allocation.keep j) ξ
      inverse_eq := fun _ _ y => original.inverse_eq reference time y
      left_eq := fun u t y => E.leftFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      right_eq := fun u t y => E.rightFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      prime_eq := fun j t y => E.slotFourierRep_eq
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ t y
      inverse_support := fun _ _ _ _ => original.inverse_support reference hreference time htime
      left_support := fun _ _ _ _ _ hy =>
        E.leftFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      right_support := fun _ _ _ _ _ hy =>
        E.rightFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      prime_support := fun j _ _ _ hy => E.slotFourierRep_support
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ
          (subset_tsupport _ hy)
      inverse_bound := fun _ _ _ _ => hinverse.trans hsize
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

theorem frozenInverseRawWindow_prime_support {target : Set ℝ}
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target)
    (ξ : WithLp 2 (ℝ × ℝ)) (j : Fin allocation.keep.card) (t : ℝ) :
    Function.support
      ((frozenInverseRawWindow P R W allocation F parent oldMoving correction hcorr C p
        leftMultiplicity rightMultiplicity pattern sector remaining extra m q index
        rectangle firstSign negative reference time original hreference htime E
        hcompact hpositive s horders hbound horiginalBound hleft hright hslot ξ).primeRep j t)
      ⊆ target :=
  (E.slotFourierRep_support_subset hcompact hpositive firstSign negative
    (SlotRestriction.index allocation.keep j) ξ).trans
    (hprime (SlotRestriction.index allocation.keep j))

end CanonicalLiteralAllocatedData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.data_pairedEnergy_inverse
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.frozenInverseRawWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.frozenInverseRawWindow_prime_support
