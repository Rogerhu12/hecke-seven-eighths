import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupportFinsets
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex

set_option linter.unusedSectionVars false

/-!
# Original norm profiles on the actual quotient column supports

Freezing the original profile's row argument is an explicit construction,
not a transformed support certificate. Division of the physical scale by
an original ideal norm reconstructs the original profile support exactly.
The genuine complete child mask supplies exterior coprimality, so the
effective child support lies in the actual exterior quotient support.

The common-support lemmas separately retain the literal extracted ideal
and its prime-to-support residual. They are finite factorization facts;
no smooth profile is asserted to vanish merely because an ideal is
removed by the arithmetic mask.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}

/-- Use the original test at the actual source row. Its norm argument,
height argument and original finite support are unchanged. -/
def fixedIdealTest (W : IdealTest K) (v : HeckeGeneral.Analysis.NonzeroIdeal K) : IdealTest K where
  profile _ t y := W.profile v t y
  support _ t N := W.support v t N
  support_spec _ t N I := W.support_spec v t N I

theorem quotient_norm_ratio (D I : HeckeGeneral.Analysis.NonzeroIdeal K) (N : ℝ) :
    idealNorm K I / (N / idealNorm K D) = idealNorm K (D * I) / N := by
  sorry

/-- Exact support reconstruction at the original divided scale. It
does not require a norm window or a positivity bound for the scale. -/
theorem fixedIdealTest_quotient_support (W : IdealTest K)
    (v u D I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    I ∈ (fixedIdealTest W v).support u t (N / idealNorm K D) ↔
      D * I ∈ W.support v t N := by
  sorry

/-- The actual exterior part of one original finite profile support. -/
def exteriorPlainSupport (W : IdealTest K) (v : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    Finset (Ideal (𝓞 K)) :=
  ((W.support v t N).filter fun I => IsCoprime I.val A.cS).image Subtype.val

@[simp] theorem mem_exteriorPlainSupport (W : IdealTest K)
    (v I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    I.val ∈ exteriorPlainSupport (A := A) W v N t ↔
      I ∈ W.support v t N ∧ IsCoprime I.val A.cS := by
  sorry

theorem exteriorPlainSupport_nonzero (W : IdealTest K)
    (v : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    ∀ I ∈ exteriorPlainSupport (A := A) W v N t, I ≠ 0 := by
  sorry

def exteriorPrimeSupport (W : PrimeWindow K) (Z t : ℝ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (W.support t (Z ^ W.length)).filter fun p => IsCoprime p.asIdeal A.cS

section ArithmeticMask

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (parent : MomentData K ω ψ) (moving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

local notation "child" => CanonicalOriginalChildData.data parent moving correction hcorr
  sector remaining budget inverse left right geometry index

/-- The effective support reads the full original mask directly. -/
theorem child_commonMask_iff (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (child).commonMask u I.val = true ↔
      sexticIdealOutsideS K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) I ∧
        IsCoprime I.val u.val ∧ IsCoprime I.val moving.support.val ∧
          IsCoprime I.val remaining.val := by
  sorry

theorem effective_plain_exterior (W : IdealTest K) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ)
    (hI : I ∈ effectivePlainSupport child W u N t) : IsCoprime I.val A.cS := by
  sorry

theorem effective_plain_full_mask (W : IdealTest K) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ)
    (hI : I ∈ effectivePlainSupport child W u N t) :
    IsCoprime I.val (moving.support.val * remaining.val) := by
  sorry

theorem effective_prime_original_support (i : Fin geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t : ℝ) :
    effectivePrimeSupport child i u Z t ⊆
      exteriorPrimeSupport (A := A) (geometry.slots i) Z t := by
  sorry

/-- This is coverage by the literal original exterior quotient
carrier, constructed from the raw original test and the actual divisor. -/
theorem effective_plain_original_quotient (W : IdealTest K)
    (v u : HeckeGeneral.Analysis.NonzeroIdeal K) (D : A.Exterior) (N t : ℝ) :
    effectivePlainSupport child (fixedIdealTest W v) u
        (N / idealNorm K (exteriorMomentIdeal D)) t ⊆
      nonzeroQuotientMomentSupport D.val (exteriorPlainSupport (A := A) W v N t) := by
  sorry

end ArithmeticMask

section CommonSupport

/-- Every prime-to-P ideal has trivial P-part, including when P is
only a subset of the support of the actual full mask. -/
theorem supportExtract_eq_one_of_coprime (I M : Ideal (𝓞 K))
    (hI : I ≠ 0) (hM : M ≠ 0) (P : Finset (Ideal (𝓞 K)))
    (hP : P ⊆ primeSupport M) (hcop : IsCoprime I M) : supportExtract I P = 1 := by
  sorry

/-- Reconstructing an original supported ideal proves membership in
the actual residual support, with no support inclusion hypothesis. -/
theorem mem_plainResidual_of_reconstruct (S P : Finset (Ideal (𝓞 K)))
    (D I : Ideal (𝓞 K)) (hD : D ≠ 0) (hI : I ≠ 0)
    (hDpart : supportExtract D P = D) (hIpart : supportExtract I P = 1)
    (hmem : D * I ∈ S) : I ∈ SupportCartesian.plainResidual S P D := by
  sorry

/-- The extracted part of an actual original ideal is supported on
the selected common-prime set, with the full original exponents. -/
theorem supportExtract_idempotent (I : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K))) :
    supportExtract (supportExtract I P) P = supportExtract I P := by
  sorry

/-- An actual divisor of a residual occurrence is still prime to the
extracted set. This supplies the allocation divisor's condition from
its original witness. -/
theorem supportExtract_eq_one_of_dvd_residual (I B : Ideal (𝓞 K))
    (hB : B ≠ 0) (P : Finset (Ideal (𝓞 K))) (hd : B ∣ supportResidual I P) :
    supportExtract B P = 1 := by
  sorry

end CommonSupport

section ActualCommonQuotients

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (parent : MomentData K ω ψ) (moving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

local notation "child" => CanonicalOriginalChildData.data parent moving correction hcorr
  sector remaining budget inverse left right geometry index

/-- All common-prime deletions are obtained from the same complete
arithmetic mask. The inclusion concerns its actual prime factors, not
a newly supplied polynomial support. -/
theorem effective_prime_original_live
    (common : Finset (Ideal (𝓞 K)))
    (hcommon : common ⊆ primeSupport (moving.support.val * remaining.val))
    (i : Fin geometry.slotCount) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t : ℝ) :
    effectivePrimeSupport child i u Z t ⊆
      SupportCartesian.primeLive
        (exteriorPrimeSupport (A := A) (geometry.slots i) Z t) common := by
  sorry

/-- The same original test produces the literal common-support
residual followed by the actual allocated quotient. Both divisions of
the scale are exact. D is the original common part and B the actual
allocated occurrence divisor. -/
theorem effective_plain_original_common_quotient (W : IdealTest K)
    (v u : HeckeGeneral.Analysis.NonzeroIdeal K) (D B : A.Exterior) (N t : ℝ)
    (common : Finset (Ideal (𝓞 K)))
    (hcommon : common ⊆ primeSupport (moving.support.val * remaining.val))
    (hDpart : supportExtract D.val common = D.val)
    (hBpart : supportExtract B.val common = 1) :
    effectivePlainSupport child (fixedIdealTest W v) u
        ((N / idealNorm K (exteriorMomentIdeal D)) /
          idealNorm K (exteriorMomentIdeal B)) t ⊆
      nonzeroQuotientMomentSupport B.val
        (SupportCartesian.plainResidual (exteriorPlainSupport (A := A) W v N t)
          common D.val) := by
  sorry

end ActualCommonQuotients

section ActualCommonMasks

open CommonSupportMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem primeSupport_mul (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    primeSupport (I * J) = primeSupport I ∪ primeSupport J := by
  sorry

/-- The first frequency's active modulus and the whole common-column
mask are jointly paid by the two original common factors. -/
theorem first_active_mul_common_mask_dvd (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) :
    (firstActiveIdeal p m n).val *
        commonRadical (primePowerProduct p m).val (primePowerProduct p n).val ∣
      (primePowerProduct p m).val * (primePowerProduct p n).val := by
  sorry

theorem first_active_mul_common_mask_norm_le (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) :
    A.exteriorNorm (firstActiveIdeal p m n) *
        (Ideal.absNorm
          (commonRadical (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) ≤
      A.exteriorNorm (primePowerProduct p m) * A.exteriorNorm (primePowerProduct p n) := by
  sorry

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- Every second common prime is present in the actual active factor
or its sixth-root remainder. This includes the principal sixth-power
case and is independent of the nonunit-pattern choice. -/
theorem second_common_subset_full_mask
    («prefix» : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (pattern : ι → Bool) :
    primeSupport (primePowerProduct p m).val ⊆
      primeSupport ((prefix.append (secondOriginalMovingFactors P R C p m n pattern)).support.val *
        (remaining.val * (secondSixthRootIdeal p m n).val)) := by
  sorry

end ActualCommonMasks

section FourierSupport

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (d : MomentData K ω ψ)
variable (left right : CanonicalLogProfiles.Atom V)
variable (slot : Fin d.geometry.slotCount → CanonicalLogProfiles.Atom V)
variable (hleft : CanonicalLogProfiles.PositivePlainProfile d.plainTest₁)
variable (hright : CanonicalLogProfiles.PositivePlainProfile d.plainTest₂)
variable (hslot : ∀ i, CanonicalLogProfiles.PositivePrimeProfile (d.geometry.slots i))

/-- The whole physical carrier is fixed before the Fourier parameter;
the actual nonzero logarithmic multiplier changes no effective support. -/
theorem effective_left_logProfiles (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    effectivePlainSupport (CanonicalLogProfiles.data d left right slot hleft hright hslot ξ)
      (CanonicalLogProfiles.data d left right slot hleft hright hslot ξ).plainTest₁ u N t =
      effectivePlainSupport d d.plainTest₁ u N t := rfl

theorem effective_right_logProfiles (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    effectivePlainSupport (CanonicalLogProfiles.data d left right slot hleft hright hslot ξ)
      (CanonicalLogProfiles.data d left right slot hleft hright hslot ξ).plainTest₂ u N t =
      effectivePlainSupport d d.plainTest₂ u N t := rfl

theorem effective_prime_logProfiles (ξ : V) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t : ℝ)
    (i : Fin d.geometry.slotCount) :
    effectivePrimeSupport (CanonicalLogProfiles.data d left right slot hleft hright hslot ξ)
      i u Z t = effectivePrimeSupport d i u Z t := rfl

end FourierSupport

end HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.effective_plain_original_quotient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.supportExtract_eq_one_of_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.mem_plainResidual_of_reconstruct
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.effective_plain_original_common_quotient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.effective_prime_original_live
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.first_active_mul_common_mask_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.second_common_subset_full_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalEffectiveChildSupport.effective_prime_logProfiles
