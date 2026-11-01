import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupportFinsets
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex

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
  have hmul : idealNorm K (D * I) = idealNorm K D * idealNorm K I := by
    change (Ideal.absNorm (D.val * I.val) : ℝ) =
      (Ideal.absNorm D.val : ℝ) * (Ideal.absNorm I.val : ℝ)
    rw [map_mul, Nat.cast_mul]
  rw [div_div_eq_mul_div, hmul]
  ring

/-- Exact support reconstruction at the original divided scale. It
does not require a norm window or a positivity bound for the scale. -/
theorem fixedIdealTest_quotient_support (W : IdealTest K)
    (v u D I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    I ∈ (fixedIdealTest W v).support u t (N / idealNorm K D) ↔
      D * I ∈ W.support v t N := by
  change I ∈ W.support v t (N / idealNorm K D) ↔ _
  rw [W.support_spec, W.support_spec, quotient_norm_ratio]

/-- The actual exterior part of one original finite profile support. -/
def exteriorPlainSupport (W : IdealTest K) (v : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    Finset (Ideal (𝓞 K)) :=
  ((W.support v t N).filter fun I => IsCoprime I.val A.cS).image Subtype.val

@[simp] theorem mem_exteriorPlainSupport (W : IdealTest K)
    (v I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    I.val ∈ exteriorPlainSupport (A := A) W v N t ↔
      I ∈ W.support v t N ∧ IsCoprime I.val A.cS := by
  rw [exteriorPlainSupport, Finset.mem_image]
  constructor
  · rintro ⟨J, hJ, he⟩
    have hJI : J = I := Subtype.ext he
    subst J
    exact Finset.mem_filter.mp hJ
  · intro h
    exact ⟨I, Finset.mem_filter.mpr h, rfl⟩

theorem exteriorPlainSupport_nonzero (W : IdealTest K)
    (v : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ) :
    ∀ I ∈ exteriorPlainSupport (A := A) W v N t, I ≠ 0 := by
  intro I hI
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact nonZeroDivisors.coe_ne_zero J

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
  simp only [CanonicalOriginalChildData.data, completeIdealCommonMask,
    sexticIdealOutsideS, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem effective_plain_exterior (W : IdealTest K) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ)
    (hI : I ∈ effectivePlainSupport child W u N t) : IsCoprime I.val A.cS := by
  have hm := effectivePlainSupport_commonMask child W u I N t hI
  exact (CanonicalOriginalPhaseCalibration.outside_iff_coprime I).mp
    ((child_commonMask_iff parent moving correction hcorr sector remaining budget
      inverse left right geometry index u I).mp hm).1

theorem effective_plain_full_mask (W : IdealTest K) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ)
    (hI : I ∈ effectivePlainSupport child W u N t) :
    IsCoprime I.val (moving.support.val * remaining.val) := by
  have hm := effectivePlainSupport_commonMask child W u I N t hI
  have hc := (child_commonMask_iff parent moving correction hcorr sector remaining budget
    inverse left right geometry index u I).mp hm
  exact hc.2.2.1.mul_right hc.2.2.2

theorem effective_prime_original_support (i : Fin geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t : ℝ) :
    effectivePrimeSupport child i u Z t ⊆
      exteriorPrimeSupport (A := A) (geometry.slots i) Z t := by
  intro p hp
  have hm := effectivePrimeSupport_commonMask child i u Z t p hp
  have hc := (child_commonMask_iff parent moving correction hcorr sector remaining budget
    inverse left right geometry index u (primeIdeal p)).mp hm
  exact Finset.mem_filter.mpr
    ⟨(effectivePrimeSupport_subset_profile child i u Z t) hp,
      (CanonicalOriginalPhaseCalibration.outside_iff_coprime (primeIdeal p)).mp hc.1⟩

/-- This is coverage by the literal original exterior quotient
carrier, constructed from the raw original test and the actual divisor. -/
theorem effective_plain_original_quotient (W : IdealTest K)
    (v u : HeckeGeneral.Analysis.NonzeroIdeal K) (D : A.Exterior) (N t : ℝ) :
    effectivePlainSupport child (fixedIdealTest W v) u
        (N / idealNorm K (exteriorMomentIdeal D)) t ⊆
      nonzeroQuotientMomentSupport D.val (exteriorPlainSupport (A := A) W v N t) := by
  intro I hI
  rw [mem_nonzeroQuotientMomentSupport D.val D.property.1]
  change (exteriorMomentIdeal D * I).val ∈ exteriorPlainSupport (A := A) W v N t
  apply (mem_exteriorPlainSupport W v (exteriorMomentIdeal D * I) N t).mpr
  refine ⟨(fixedIdealTest_quotient_support W v u (exteriorMomentIdeal D) I N t).mp
    ((effectivePlainSupport_subset_profile child (fixedIdealTest W v) u _ t) hI), ?_⟩
  exact (Ideal.isCoprime_iff_sup_eq.mpr D.property.2).mul_left
    (effective_plain_exterior parent moving correction hcorr sector remaining budget
      inverse left right geometry index (fixedIdealTest W v) u I _ t hI)

end ArithmeticMask

section CommonSupport

/-- Every prime-to-P ideal has trivial P-part, including when P is
only a subset of the support of the actual full mask. -/
theorem supportExtract_eq_one_of_coprime (I M : Ideal (𝓞 K))
    (hI : I ≠ 0) (hM : M ≠ 0) (P : Finset (Ideal (𝓞 K)))
    (hP : P ⊆ primeSupport M) (hcop : IsCoprime I M) : supportExtract I P = 1 := by
  have hd := (primeSupport_disjoint_iff hI hM).mpr hcop
  have hr : supportResidual I P = I := by
    change ((normalizedFactors I).filter (fun Q => Q ∉ P)).prod = I
    rw [Multiset.filter_eq_self.mpr (by
      intro Q hQ hQP
      exact Finset.disjoint_left.mp hd (Multiset.mem_toFinset.mpr hQ) (hP hQP))]
    exact Ideal.prod_normalizedFactors_eq_self hI
  apply mul_right_cancel₀ hI
  simpa only [hr, one_mul] using support_reconstruct I hI P

/-- Reconstructing an original supported ideal proves membership in
the actual residual support, with no support inclusion hypothesis. -/
theorem mem_plainResidual_of_reconstruct (S P : Finset (Ideal (𝓞 K)))
    (D I : Ideal (𝓞 K)) (hD : D ≠ 0) (hI : I ≠ 0)
    (hDpart : supportExtract D P = D) (hIpart : supportExtract I P = 1)
    (hmem : D * I ∈ S) : I ∈ SupportCartesian.plainResidual S P D := by
  have hpart : supportExtract (D * I) P = D := by
    rw [supportExtract_mul D I hD hI, hDpart, hIpart, mul_one]
  have hr : supportResidual (D * I) P = I := by
    apply mul_left_cancel₀ hD
    simpa only [hpart] using support_reconstruct (D * I) (mul_ne_zero hD hI) P
  exact Finset.mem_image.mpr
    ⟨D * I, Finset.mem_filter.mpr ⟨hmem, hpart⟩, hr⟩

/-- The extracted part of an actual original ideal is supported on
the selected common-prime set, with the full original exponents. -/
theorem supportExtract_idempotent (I : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K))) :
    supportExtract (supportExtract I P) P = supportExtract I P := by
  change ((normalizedFactors (supportExtract I P)).filter (fun Q => Q ∈ P)).prod = _
  rw [supportExtract_factors]
  simpa only [Multiset.filter_filter, and_self]

/-- An actual divisor of a residual occurrence is still prime to the
extracted set. This supplies the allocation divisor's condition from
its original witness. -/
theorem supportExtract_eq_one_of_dvd_residual (I B : Ideal (𝓞 K))
    (hB : B ≠ 0) (P : Finset (Ideal (𝓞 K))) (hd : B ∣ supportResidual I P) :
    supportExtract B P = 1 := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hB
    (supportResidual_ne_zero I P)).mp hd
  have hr : supportResidual B P = B := by
    change ((normalizedFactors B).filter (fun Q => Q ∉ P)).prod = B
    rw [Multiset.filter_eq_self.mpr (by
      intro Q hQ
      have hres : Q ∈ primeSupport (supportResidual I P) :=
        Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf hQ)
      rw [supportResidual_support] at hres
      exact (Finset.mem_sdiff.mp hres).2)]
    exact Ideal.prod_normalizedFactors_eq_self hB
  apply mul_right_cancel₀ hB
  simpa only [hr, one_mul] using support_reconstruct B hB P

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
  intro p hp
  have hm := effectivePrimeSupport_commonMask child i u Z t p hp
  have hc := (child_commonMask_iff parent moving correction hcorr sector remaining budget
    inverse left right geometry index u (primeIdeal p)).mp hm
  have hpart := supportExtract_eq_one_of_coprime p.asIdeal
    (moving.support.val * remaining.val) p.ne_bot
    (mul_ne_zero moving.support.property.1 (nonZeroDivisors.coe_ne_zero remaining))
    common hcommon (hc.2.2.1.mul_right hc.2.2.2)
  exact Finset.mem_filter.mpr
    ⟨effective_prime_original_support parent moving correction hcorr sector remaining budget
      inverse left right geometry index i u Z t hp,
      (SupportCartesian.prime_extract_eq_one p common).mp hpart⟩

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
  intro I hI
  rw [mem_nonzeroQuotientMomentSupport B.val B.property.1]
  have hcop := effective_plain_full_mask parent moving correction hcorr sector remaining budget
    inverse left right geometry index (fixedIdealTest W v) u I _ t hI
  have hIpart := supportExtract_eq_one_of_coprime I.val
    (moving.support.val * remaining.val) (nonZeroDivisors.coe_ne_zero I)
    (mul_ne_zero moving.support.property.1 (nonZeroDivisors.coe_ne_zero remaining))
    common hcommon hcop
  have hBIpart : supportExtract (B.val * I.val) common = 1 := by
    rw [supportExtract_mul B.val I.val B.property.1 (nonZeroDivisors.coe_ne_zero I),
      hBpart, hIpart, one_mul]
  apply mem_plainResidual_of_reconstruct _ common D.val (B.val * I.val)
    D.property.1 (mul_ne_zero B.property.1 (nonZeroDivisors.coe_ne_zero I))
    hDpart hBIpart
  change (exteriorMomentIdeal D * (exteriorMomentIdeal B * I)).val ∈
    exteriorPlainSupport (A := A) W v N t
  apply (mem_exteriorPlainSupport W v _ N t).mpr
  constructor
  · have hp := (effectivePlainSupport_subset_profile child (fixedIdealTest W v) u _ t) hI
    have hBprofile := (fixedIdealTest_quotient_support W v u
      (exteriorMomentIdeal B) I (N / idealNorm K (exteriorMomentIdeal D)) t).mp hp
    exact (fixedIdealTest_quotient_support W v u
      (exteriorMomentIdeal D) (exteriorMomentIdeal B * I) N t).mp hBprofile
  · exact (Ideal.isCoprime_iff_sup_eq.mpr D.property.2).mul_left
      ((Ideal.isCoprime_iff_sup_eq.mpr B.property.2).mul_left
        (effective_plain_exterior parent moving correction hcorr sector remaining budget
          inverse left right geometry index (fixedIdealTest W v) u I _ t hI))

end ActualCommonQuotients

section ActualCommonMasks

open CommonSupportMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem primeSupport_mul (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    primeSupport (I * J) = primeSupport I ∪ primeSupport J := by
  simp only [primeSupport, normalizedFactors_mul hI hJ, Multiset.toFinset_add]

/-- The first frequency's active modulus and the whole common-column
mask are jointly paid by the two original common factors. -/
theorem first_active_mul_common_mask_dvd (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) :
    (firstActiveIdeal p m n).val *
        commonRadical (primePowerProduct p m).val (primePowerProduct p n).val ∣
      (primePowerProduct p m).val * (primePowerProduct p n).val :=
  mul_dvd_mul (firstActiveIdeal_dvd_common p m n hm)
    (commonRadical_dvd _ _ (primePowerProduct p m).property.1
      (primePowerProduct p n).property.1).2

theorem first_active_mul_common_mask_norm_le (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) :
    A.exteriorNorm (firstActiveIdeal p m n) *
        (Ideal.absNorm
          (commonRadical (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) ≤
      A.exteriorNorm (primePowerProduct p m) * A.exteriorNorm (primePowerProduct p n) := by
  have h := norm_le_of_dvd
    (mul_ne_zero (primePowerProduct p m).property.1 (primePowerProduct p n).property.1)
    (first_active_mul_common_mask_dvd p m n hm)
  simpa only [map_mul, Nat.cast_mul] using h

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- Every second common prime is present in the actual active factor
or its sixth-root remainder. This includes the principal sixth-power
case and is independent of the nonunit-pattern choice. -/
theorem second_common_subset_full_mask
    (prefix : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (pattern : ι → Bool) :
    primeSupport (primePowerProduct p m).val ⊆
      primeSupport ((prefix.append (secondOriginalMovingFactors P R C p m n pattern)).support.val *
        (remaining.val * (secondSixthRootIdeal p m n).val)) := by
  let D := secondOriginalMovingFactors P R C p m n pattern
  rw [primeSupport_mul _ _ (prefix.append D).support.property.1
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero remaining) (secondSixthRootIdeal p m n).property.1),
    prefix.append_support_primes D,
    primeSupport_mul _ _ (nonZeroDivisors.coe_ne_zero remaining)
      (secondSixthRootIdeal p m n).property.1]
  intro Q hQ
  rw [primePowerProduct_support_nonzero p hp] at hQ
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
  by_cases hroot : min (m i) (n i) / 6 = 0
  · have hmin : 0 < min (m i) (n i) := lt_min (hm i) (hn i)
    have hactive : secondActiveExponent m n pattern i ≠ 0 := by
      simp only [secondActiveExponent]
      split_ifs <;> omega
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    rw [D.support_primes]
    change (p i).val.asIdeal ∈ primeSupport
      (OriginalMovingFactors.singleton (P := P) (R := R)
        ⟨secondActiveFrequencyGenerator C p m n pattern,
          (secondActiveFrequencyGenerator_generates C p m n pattern).1⟩ 1).fullIdeal.val
    rw [OriginalMovingFactors.singleton_fullIdeal (P := P) (R := R)
      (secondActiveFrequencyIdeal p m n pattern) (secondActiveFrequencyGenerator C p m n pattern)
      (secondActiveFrequencyGenerator_generates C p m n pattern) 1]
    change (p i).val.asIdeal ∈ primeSupport (primePowerProduct p (secondActiveExponent m n pattern)).val
    rw [primePowerProduct_support_nonzero p hp]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hactive⟩, rfl⟩
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    right
    change (p i).val.asIdeal ∈ primeSupport (primePowerProduct p (fun j => min (m j) (n j) / 6)).val
    rw [primePowerProduct_support_nonzero p hp]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hroot⟩, rfl⟩

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
