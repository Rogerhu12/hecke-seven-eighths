import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEffectiveChildSupport
import HeckePort.Moments.Descent.MarkedTwists

/-!
# The original common-column deletion in the child remaining mask

Common-support extraction removes every common prime from each residual
occurrence, including the primes with principal first character. The
chosen divisor of the first frequency mask need not contain those primes.

This module retains the original common-left ideal in `remaining`.
The complete child support later takes the radical of that literal
product. The moving factor list and its character are unchanged. On
the actual residual columns the additional mask is one, proved from
their definitions, so all source atoms and the complete centered
subtraction are retained exactly. The full mask must still be included
in the joint row budget; no norm estimate is inferred from this identity.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalCommonColumnMask

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid
open CanonicalOriginalPhaseCalibration CanonicalSecondFactorAssembly

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

theorem supportExtract_own_support (D : A.Exterior) :
    supportExtract D.val (primeSupport D.val) = D.val := by
  change ((normalizedFactors D.val).filter (fun Q => Q ∈ primeSupport D.val)).prod = D.val
  rw [Multiset.filter_eq_self.mpr (by
    intro Q hQ
    exact Multiset.mem_toFinset.mpr hQ)]
  exact Ideal.prod_normalizedFactors_eq_self D.property.1

theorem residual_coprime (D : A.Exterior) (I : Ideal (𝓞 K)) :
    IsCoprime (supportResidual I (primeSupport D.val)) D.val := by
  have h := (extracted_residual_coprime D.val I (primeSupport D.val)).symm
  rwa [supportExtract_own_support D] at h

theorem plainResidual_coprime (D : A.Exterior) (S : Finset (Ideal (𝓞 K)))
    (part I : Ideal (𝓞 K)) (hI : I ∈ SupportCartesian.plainResidual S (primeSupport D.val) part) :
    IsCoprime (sourceMomentIdeal I).val D.val := by
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  rw [sourceMomentIdeal_val_of_ne_zero _ (supportResidual_ne_zero _ _)]
  exact residual_coprime D J

theorem primeLive_coprime (D : A.Exterior) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ SupportCartesian.primeLive S (primeSupport D.val)) : IsCoprime p.asIdeal D.val := by
  apply (prime_isCoprime_iff_not_dvd p.asIdeal D.val p.prime).mpr
  intro hd
  exact (Finset.mem_filter.mp hp).2
    ((prime_mem_support_iff_dvd p.asIdeal D.val p.prime D.property.1).mpr hd)

variable (moving : OriginalMovingFactors A P R) (remaining : NonzeroIdeal K)
variable (D : A.Exterior)

/-- The entire original common part remains visible to the full-mask
budget. Its multiplicities do not create repeated support charges. -/
theorem coprime_movingMask_common (I : Ideal (𝓞 K)) :
    IsCoprime I (movingMask moving (remaining * exteriorMomentIdeal D)).val ↔
      IsCoprime I (movingMask moving remaining).val ∧ IsCoprime I D.val := by
  simp only [movingMask, IsCoprime.mul_right_iff]
  tauto

theorem maskValue_preserved (I : Ideal (𝓞 K)) (hI : IsCoprime I D.val) :
    originalCoprimeMask (movingMask moving (remaining * exteriorMomentIdeal D)) I =
      originalCoprimeMask (movingMask moving remaining) I := by
  change (if IsCoprime I (movingMask moving (remaining * exteriorMomentIdeal D)).val
      then (1 : ℂ) else 0) = _
  rw [coprime_movingMask_common moving remaining D]
  simp only [hI, and_true]

/-- The actual full mask now covers all of the original common
support. This is derived from the displayed remaining ideal. -/
theorem common_support_subset :
    primeSupport D.val ⊆
      primeSupport (moving.support.val * (remaining * exteriorMomentIdeal D).val) := by
  intro Q hQ
  have hprime := support_prime hQ
  have hd := (prime_mem_support_iff_dvd Q D.val hprime D.property.1).mp hQ
  apply (prime_mem_support_iff_dvd Q _ hprime
    (mul_ne_zero moving.support.property.1
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero remaining) D.property.1))).mpr
  exact hd.trans ((dvd_mul_left D.val remaining.val).trans
    (dvd_mul_left (remaining.val * D.val) moving.support.val))

theorem fullMaskSupport_common_primes :
    primeSupport (moving.fullMaskSupport (remaining * exteriorMomentIdeal D)).val =
      primeSupport (moving.fullMaskSupport remaining).val ∪ primeSupport D.val := by
  rw [moving.fullMaskSupport_primes (remaining * exteriorMomentIdeal D),
    moving.fullMaskSupport_primes remaining]
  simp only [primeSupport,
    normalizedFactors_mul (nonZeroDivisors.coe_ne_zero remaining) D.property.1,
    Multiset.toFinset_add, Finset.union_assoc]

/-- Only the radical of the true common part is paid, even though
the complete original ideal is retained in the remaining field. -/
theorem fullMaskSupport_common_dvd :
    (moving.fullMaskSupport (remaining * exteriorMomentIdeal D)).val ∣
      (moving.fullMaskSupport remaining).val * CommonSupportMass.commonRadical D.val D.val := by
  let M := moving.fullMaskSupport remaining
  let C := CommonSupportMass.commonRadical D.val D.val
  have hM : M.val ≠ 0 := nonZeroDivisors.coe_ne_zero M
  have hC : C ≠ 0 := CommonSupportMass.commonRadical_ne_zero _ _
  rw [← squarefree_support_product_self
    (moving.fullMaskSupport_squarefree (remaining * exteriorMomentIdeal D))]
  apply support_product_dvd (mul_ne_zero hM hC)
  intro Q hQ
  rw [fullMaskSupport_common_primes moving remaining D] at hQ
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · have hp := support_prime hQ
    apply (prime_mem_support_iff_dvd Q _ hp (mul_ne_zero hM hC)).mpr
    exact ((prime_mem_support_iff_dvd Q M.val hp hM).mp hQ).trans (dvd_mul_right M.val C)
  · have hp := support_prime hQ
    have hQC : Q ∈ primeSupport C := by
      dsimp only [C]
      rw [CommonSupportMass.commonRadical_support, Finset.inter_self]
      exact hQ
    apply (prime_mem_support_iff_dvd Q _ hp (mul_ne_zero hM hC)).mpr
    exact ((prime_mem_support_iff_dvd Q C hp hC).mp hQC).trans (dvd_mul_left C M.val)

theorem fullMaskSupport_common_norm_le :
    idealNorm K (moving.fullMaskSupport (remaining * exteriorMomentIdeal D)) ≤
      idealNorm K (moving.fullMaskSupport remaining) *
        (Ideal.absNorm (CommonSupportMass.commonRadical D.val D.val) : ℝ) := by
  have h := norm_le_of_dvd
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero (moving.fullMaskSupport remaining))
      (CommonSupportMass.commonRadical_ne_zero D.val D.val))
    (fullMaskSupport_common_dvd moving remaining D)
  simpa only [map_mul, Nat.cast_mul] using h

variable {k : ℕ}
variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (index : Fin k → Fin parent.geometry.slotCount)

theorem sourcePlain_preserved (I : NonzeroIdeal K) (hI : IsCoprime I.val D.val) :
    sourcePlainCoefficient
        (movingSourceCharacters parent correction moving (remaining * exteriorMomentIdeal D) index).plain
        (movingSourceCharacters parent correction moving (remaining * exteriorMomentIdeal D) index).plainTwist
        (movingSourceCharacters parent correction moving (remaining * exteriorMomentIdeal D) index).mask I =
      sourcePlainCoefficient
        (movingSourceCharacters parent correction moving remaining index).plain
        (movingSourceCharacters parent correction moving remaining index).plainTwist
        (movingSourceCharacters parent correction moving remaining index).mask I := by
  simp only [sourcePlainCoefficient, movingSourceCharacters, sourceCharacters,
    maskValue_preserved moving remaining D I.val hI]

theorem sourcePrime_preserved (i : Fin k) (p : HeightOneSpectrum (𝓞 K))
    (hp : IsCoprime p.asIdeal D.val) :
    sourcePrimeCoefficient
        ((movingSourceCharacters parent correction moving (remaining * exteriorMomentIdeal D) index).slot i)
        ((movingSourceCharacters parent correction moving (remaining * exteriorMomentIdeal D) index).slotTwist i)
        (movingSourceCharacters parent correction moving (remaining * exteriorMomentIdeal D) index).mask p =
      sourcePrimeCoefficient
        ((movingSourceCharacters parent correction moving remaining index).slot i)
        ((movingSourceCharacters parent correction moving remaining index).slotTwist i)
        (movingSourceCharacters parent correction moving remaining index).mask p := by
  simp only [sourcePrimeCoefficient, movingSourceCharacters, sourceCharacters,
    maskValue_preserved moving remaining D p.asIdeal hp]

section Dictionaries

variable {Ray : Type*} [CommGroup Ray] (phase : Ray →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (part₁ part₂ : Ideal (𝓞 K))

local notation "T" => movingSourceCharacters parent correction moving remaining index
local notation "T'" => movingSourceCharacters parent correction moving
  (remaining * exteriorMomentIdeal D) index
local notation "L" => SupportCartesian.plainResidual S₁ (primeSupport D.val) part₁
local notation "R'" => SupportCartesian.plainResidual S₂ (primeSupport D.val) part₂
local notation "Slots" => fun i => SupportCartesian.primeLive (S i) (primeSupport D.val)

variable (F : SecondCoefficientTermDictionary T phase L R' Slots)

/-- The original atoms acquire their actual common deletion solely
through the already fixed residual carriers. There is no new atom
identity input and no new scalar factor. -/
def dictionary : SecondCoefficientTermDictionary T' phase L R' Slots where
  leftAtom := F.leftAtom
  rightAtom := F.rightAtom
  slotAtom := F.slotAtom
  leftRay := F.leftRay
  rightRay := F.rightRay
  slotRay := F.slotRay
  scale₁ := F.scale₁
  scale₂ := F.scale₂
  base := F.base
  length := F.length
  leftWeight := F.leftWeight
  rightWeight := F.rightWeight
  slotWeight := F.slotWeight
  plain₁ I hI := by
    rw [sourcePlain_preserved moving remaining D parent correction index
      (sourceMomentIdeal I) (plainResidual_coprime D S₁ part₁ I hI)]
    exact F.plain₁ I hI
  plain₂ I hI := by
    rw [sourcePlain_preserved moving remaining D parent correction index
      (sourceMomentIdeal I) (plainResidual_coprime D S₂ part₂ I hI)]
    exact F.plain₂ I hI
  prime i p hp := by
    rw [sourcePrime_preserved moving remaining D parent correction index i p
      (primeLive_coprime D (S i) p hp)]
    exact F.prime i p hp

@[simp] theorem dictionary_coefficient (i : AllocationColumn K k) :
    (dictionary moving remaining D parent correction index phase S₁ S₂ S part₁ part₂ F).coefficient i =
      F.coefficient i := rfl

@[simp] theorem dictionary_ray (i : AllocationColumn K k) :
    (dictionary moving remaining D parent correction index phase S₁ S₂ S part₁ part₂ F).ray i =
      F.ray i := rfl

def comparison (E : SecondCoefficientComparison F) :
    SecondCoefficientComparison
      (dictionary moving remaining D parent correction index phase S₁ S₂ S part₁ part₂ F) where
  leftAtom := E.leftAtom
  rightAtom := E.rightAtom
  scale₁ := E.scale₁
  scale₂ := E.scale₂
  leftWeight := E.leftWeight
  rightWeight := E.rightWeight
  plain₁ I hI := by
    rw [sourcePlain_preserved moving remaining D parent correction index
      (sourceMomentIdeal I) (plainResidual_coprime D S₁ part₁ I hI)]
    exact E.plain₁ I hI
  plain₂ I hI := by
    rw [sourcePlain_preserved moving remaining D parent correction index
      (sourceMomentIdeal I) (plainResidual_coprime D S₂ part₂ I hI)]
    exact E.plain₂ I hI

/-- The centered difference is kept intact before every later norm
or energy inequality, using the same original Gauss normalizers. -/
@[simp] theorem comparison_centeredCoefficient (E : SecondCoefficientComparison F)
    (u v : ℂ) (t : Fin k → ℂ) (i : AllocationColumn K k) :
    (comparison moving remaining D parent correction index phase S₁ S₂ S part₁ part₂ F E).
      centeredCoefficient u v t i = E.centeredCoefficient u v t i := rfl

end Dictionaries

end HeckeSkeleton.Moments.EngineStep.CanonicalCommonColumnMask

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCommonColumnMask.common_support_subset
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCommonColumnMask.fullMaskSupport_common_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCommonColumnMask.dictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCommonColumnMask.comparison_centeredCoefficient
