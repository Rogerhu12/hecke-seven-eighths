import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalAppendedPhaseCalibration

/-!
# The support actually excluded by the literal child mask

At an original common prime, the active exponent and the complete sixth
root together have positive multiplicity.  This remains true when the
active exponent vanishes.  Consequently the actual child mask excludes
every prime of both original common ideals, for every Boolean pattern.

The old displayed factors and the original remaining ideal are also
retained.  Replacing the remaining ideal by its exterior radical is used
only through the exact complete-row mask identity.  These are consequences
of the nonzero literal mask; no live-row, nonempty-row, finite-support, or
whole-polynomial hypothesis is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The active remainder and the full sixth root cover an original
prime even for an arbitrary, possibly unrealized, nonunit pattern. -/
theorem active_add_root_positive (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (pattern : Bool) :
    1 ≤ (min m n % 6 + if pattern then 1 else 0) + min m n / 6 := by
  have hmin : 0 < min m n := lt_min hm hn
  split_ifs <;> omega

/-- This stronger product divisibility does not require the prime list
to be injective.  It therefore also supplies the support argument without
using any correlation or row condition. -/
theorem prime_product_dvd_active_root
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    (primePowerProduct p (fun _ => 1)).val ∣
      (secondActiveFrequencyIdeal p m n pattern).val *
        (secondSixthRootIdeal p m n).val := by
  unfold secondActiveFrequencyIdeal secondSixthRootIdeal
  rw [← primePowerProduct_add]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ =>
    pow_dvd_pow _ (active_add_root_positive (m i) (n i) (hm i) (hn i) (pattern i)))

/-- In the actual injective prime dictionary, the preceding product is
the radical of the two common ideals. -/
theorem common_radical_dvd_active_root
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    commonRadical (primePowerProduct p m).val (primePowerProduct p n).val ∣
      (secondActiveFrequencyIdeal p m n pattern).val *
        (secondSixthRootIdeal p m n).val := by
  rw [commonRadical_primePowerProduct p hp m n hm hn]
  have h := prime_product_dvd_active_root p m n pattern hm hn
  change (∏ i, (p i).val.asIdeal ^ 1) ∣ _ at h
  simpa only [pow_one] using h

theorem coprime_each_prime_of_active_root
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (I : Ideal (𝓞 K))
    (hactive : IsCoprime I (secondActiveFrequencyIdeal p m n pattern).val)
    (hroot : IsCoprime I (secondSixthRootIdeal p m n).val) (i : ι) :
    IsCoprime I (p i).val.asIdeal := by
  have hall := (hactive.mul_right hroot).of_isCoprime_of_dvd_right
    (prime_product_dvd_active_root p m n pattern hm hn)
  change IsCoprime I (∏ j, (p j).val.asIdeal ^ 1) at hall
  simpa only [pow_one] using hall.of_prod_right i (Finset.mem_univ i)

theorem coprime_common_of_active_root
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (I : Ideal (𝓞 K))
    (hactive : IsCoprime I (secondActiveFrequencyIdeal p m n pattern).val)
    (hroot : IsCoprime I (secondSixthRootIdeal p m n).val) :
    IsCoprime I (primePowerProduct p m).val ∧
      IsCoprime I (primePowerProduct p n).val := by
  have hi := coprime_each_prime_of_active_root p m n pattern hm hn I hactive hroot
  constructor
  · change IsCoprime I (∏ i, (p i).val.asIdeal ^ m i)
    exact IsCoprime.prod_right (fun i _ => (hi i).pow_right)
  · change IsCoprime I (∏ i, (p i).val.asIdeal ^ n i)
    exact IsCoprime.prod_right (fun i _ => (hi i).pow_right)

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The primitive coprimalities recovered from one actual nonzero mask.
This record is an output of `childData_mask_nonzero`, not an input to the
construction of the child or its finite support. -/
structure MaskConsequences (oldMoving : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) : Prop where
  fixed : IsCoprime I.val A.cS
  row : IsCoprime I.val u.val
  old_support : IsCoprime I.val oldMoving.support.val
  old_remaining : IsCoprime I.val remaining.val
  active : IsCoprime I.val (secondActiveFrequencyIdeal p m n pattern).val
  root : IsCoprime I.val (secondSixthRootIdeal p m n).val

namespace MaskConsequences

variable {oldMoving : OriginalMovingFactors A P R}
variable {remaining : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {p : ι → ExteriorPrime A} {m n : ι → ℕ} {pattern : ι → Bool}
variable {u I : HeckeGeneral.Analysis.NonzeroIdeal K}
variable (H : MaskConsequences oldMoving remaining p m n pattern u I)
include H

theorem old_full_support :
    IsCoprime I.val (oldMoving.fullMaskSupport remaining).val :=
  (oldMoving.fullMaskSupport_coprime_iff remaining I.val).mpr
    ⟨H.old_support, H.old_remaining⟩

theorem old_full_support_prime (q : Ideal (𝓞 K))
    (hq : q ∈ primeSupport (oldMoving.fullMaskSupport remaining).val) :
    IsCoprime I.val q :=
  (coprime_support_iff I.val (oldMoving.fullMaskSupport remaining).val
    (nonZeroDivisors.ne_zero (oldMoving.fullMaskSupport remaining).property)).mp
      H.old_full_support q hq

/-- In particular every first or pool singleton previously appended to
the moving list remains excluded, including exponent-zero occurrences. -/
theorem old_factor (i : Fin oldMoving.count) :
    IsCoprime I.val (oldMoving.factorIdeal i).val := by
  have hfull := (oldMoving.coprime_support_iff_fullIdeal I.val).mp H.old_support
  change IsCoprime I.val (∏ j, (oldMoving.factorIdeal j).val) at hfull
  exact hfull.of_prod_right i (Finset.mem_univ i)

theorem old_factor_prime (i : Fin oldMoving.count) (q : Ideal (𝓞 K))
    (hq : q ∈ primeSupport (oldMoving.factorIdeal i).val) :
    IsCoprime I.val q :=
  (coprime_support_iff I.val (oldMoving.factorIdeal i).val
    (oldMoving.factorIdeal i).property.1).mp (H.old_factor i) q hq

theorem second_prime (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (i : ι) :
    IsCoprime I.val (p i).val.asIdeal :=
  coprime_each_prime_of_active_root p m n pattern hm hn I.val H.active H.root i

theorem second_common (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    IsCoprime I.val (primePowerProduct p m).val ∧
      IsCoprime I.val (primePowerProduct p n).val :=
  coprime_common_of_active_root p m n pattern hm hn I.val H.active H.root

theorem second_left_prime (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (q : Ideal (𝓞 K)) (hq : q ∈ primeSupport (primePowerProduct p m).val) :
    IsCoprime I.val q :=
  (coprime_support_iff I.val (primePowerProduct p m).val
    (primePowerProduct p m).property.1).mp (H.second_common hm hn).1 q hq

theorem second_right_prime (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (q : Ideal (𝓞 K)) (hq : q ∈ primeSupport (primePowerProduct p n).val) :
    IsCoprime I.val q :=
  (coprime_support_iff I.val (primePowerProduct p n).val
    (primePowerProduct p n).property.1).mp (H.second_common hm hn).2 q hq

end MaskConsequences

variable {ω ψ : HeckeCharacter K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

/-- Recover the original coprimality conditions from the same child
used by the actual appended phase calibration. -/
theorem childData_mask_nonzero (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue
      (CanonicalAppendedPhaseCalibration.childData P R parent oldMoving correction hcorr
        C p m n pattern ν remaining budget inverse left right geometry index) u I.val ≠ 0) :
    MaskConsequences oldMoving remaining p m n pattern u I := by
  rw [CanonicalAppendedPhaseCalibration.childData_mask_eq P R parent oldMoving correction
      hcorr C p m n pattern ν remaining budget inverse left right geometry index u I,
    CanonicalOriginalPhaseCalibration.childData_mask P R parent correction hcorr C p m n
      pattern ν (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)) budget
      inverse left right geometry index u I] at hmask
  have hgood :
      CanonicalOriginalPhaseCalibration.phaseMask u
          (secondOriginalMovingFactors P R C p m n pattern).support.val
          (secondSixthRootIdeal p m n) I ∧
        IsCoprime I.val (oldMoving.effectiveFullSupport remaining).val := by
    by_contra hn
    exact hmask (if_neg hn)
  have hfixed : IsCoprime I.val A.cS :=
    (CanonicalOriginalPhaseCalibration.outside_iff_coprime I).mp hgood.1.1
  have hold : IsCoprime I.val oldMoving.support.val :=
    hgood.2.of_isCoprime_of_dvd_right
      (oldMoving.support_dvd_effectiveFullSupport remaining)
  have hremaining : IsCoprime I.val remaining.val :=
    (remainingMaskRadical_coprime_iff A remaining I.val hfixed).mpr
      (hgood.2.of_isCoprime_of_dvd_right
        (oldMoving.remainingMaskIdeal_dvd_effectiveFullSupport remaining))
  have hactive : IsCoprime I.val (secondActiveFrequencyIdeal p m n pattern).val := by
    have h := ((secondOriginalMovingFactors P R C p m n pattern).coprime_support_iff_fullIdeal
      I.val).mp hgood.1.2.2.1
    have hfull : (secondOriginalMovingFactors P R C p m n pattern).fullIdeal =
        secondActiveFrequencyIdeal p m n pattern :=
      OriginalMovingFactors.singleton_fullIdeal (secondActiveFrequencyIdeal p m n pattern)
        (secondActiveFrequencyGenerator C p m n pattern)
        (secondActiveFrequencyGenerator_generates C p m n pattern) 1
    simpa only [hfull] using h
  exact ⟨hfixed, hgood.1.2.1, hold, hremaining, hactive, hgood.1.2.2.2⟩

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport.active_add_root_positive
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport.common_radical_dvd_active_root
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport.childData_mask_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport.MaskConsequences.old_full_support_prime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport.MaskConsequences.old_factor_prime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMaskSupport.MaskConsequences.second_common
