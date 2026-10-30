import HeckeGeneral.Analysis.SixthPowerFreeFactorization
import HeckeGeneral.Analysis.LocalThetaInput

/-!
Actual sixth-power-free decomposition of nonzero integral ideals.
The base and amplifier use the remainder and quotient of each prime
exponent. This is an ideal construction, with no choice of generators.
It does not assert that frequency rows cover all S-integer orbits.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The actual ideal with each prime exponent reduced modulo six. -/
def sixthPowerFreePart (I : NonzeroIdeal K) : NonzeroIdeal K :=
  idealOfPrimeExponents ((primeExponents I).mapRange (fun n => n % 6) (by decide))

/-- The actual ideal with each prime exponent divided by six. -/
def sixthPowerAmplifierPart (I : NonzeroIdeal K) : NonzeroIdeal K :=
  idealOfPrimeExponents ((primeExponents I).mapRange (fun n => n / 6) (by decide))

@[simp] theorem primeExponents_sixthPowerFreePart (I : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents (sixthPowerFreePart I) p = primeExponents I p % 6 := by
  simp only [sixthPowerFreePart, primeExponents_idealOfPrimeExponents,
    Finsupp.mapRange_apply]

@[simp] theorem primeExponents_sixthPowerAmplifierPart (I : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents (sixthPowerAmplifierPart I) p = primeExponents I p / 6 := by
  simp only [sixthPowerAmplifierPart, primeExponents_idealOfPrimeExponents,
    Finsupp.mapRange_apply]

theorem sixthPowerFreePart_isSixthPowerFree (I : NonzeroIdeal K) :
    SixthPowerFreeIdeal (sixthPowerFreePart I) := by
  rw [sixthPowerFreeIdeal_iff_primeExponents_lt]
  intro p
  rw [primeExponents_sixthPowerFreePart]
  exact Nat.mod_lt _ (by decide)

theorem sixthPowerFreePart_mul_amplifier_sixth (I : NonzeroIdeal K) :
    sixthPowerFreePart I * sixthPowerAmplifierPart I ^ 6 = I := by
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  apply Finsupp.ext
  intro p
  change primeExponents (sixthPowerFreePart I * sixthPowerAmplifierPart I ^ 6) p =
    primeExponents I p
  rw [primeExponents_mul, Finsupp.add_apply, primeExponents_pow_apply,
    primeExponents_sixthPowerFreePart, primeExponents_sixthPowerAmplifierPart]
  omega

theorem sixthPowerFreePart_dvd (I : NonzeroIdeal K) :
    (sixthPowerFreePart I).val ∣ I.val := by
  refine ⟨(sixthPowerAmplifierPart I).val ^ 6, ?_⟩
  exact (congrArg Subtype.val (sixthPowerFreePart_mul_amplifier_sixth I)).symm

theorem sixthPowerAmplifierPart_dvd (I : NonzeroIdeal K) :
    (sixthPowerAmplifierPart I).val ∣ I.val := by
  refine ⟨(sixthPowerFreePart I).val * (sixthPowerAmplifierPart I).val ^ 5, ?_⟩
  have h := congrArg Subtype.val (sixthPowerFreePart_mul_amplifier_sixth I)
  change (sixthPowerFreePart I).val * (sixthPowerAmplifierPart I).val ^ 6 = I.val at h
  rw [← h]
  ring

theorem idealNorm_sixthPowerFree_decomposition (I : NonzeroIdeal K) :
    idealNorm K I = idealNorm K (sixthPowerFreePart I) *
      idealNorm K (sixthPowerAmplifierPart I) ^ 6 := by
  calc
    idealNorm K I = idealNorm K (sixthPowerFreePart I * sixthPowerAmplifierPart I ^ 6) :=
      congrArg (idealNorm K) (sixthPowerFreePart_mul_amplifier_sixth I).symm
    _ = _ := by
      simp only [idealNorm, Submonoid.coe_mul, SubmonoidClass.coe_pow,
        map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

/-- Existence complements the previously proved arithmetic uniqueness. -/
theorem exists_unique_sixthPowerFree_decomposition (I : NonzeroIdeal K) :
    ∃! x : {J : NonzeroIdeal K // SixthPowerFreeIdeal J} × NonzeroIdeal K,
      x.1.val * x.2 ^ 6 = I := by
  refine ⟨(⟨sixthPowerFreePart I, sixthPowerFreePart_isSixthPowerFree I⟩,
    sixthPowerAmplifierPart I), sixthPowerFreePart_mul_amplifier_sixth I, ?_⟩
  intro x hx
  obtain ⟨hbase, hamp⟩ := sixthPowerFree_mul_sixth_unique x.1.property
    (sixthPowerFreePart_isSixthPowerFree I)
    (hx.trans (sixthPowerFreePart_mul_amplifier_sixth I).symm)
  exact Prod.ext (Subtype.ext hbase) hamp

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem sixthPowerFreePart_outsideS (I : ExteriorIdeal K S) :
    ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ (sixthPowerFreePart I.val).val → p ∉ S := by
  intro p hp
  exact I.property p (dvd_trans hp (sixthPowerFreePart_dvd I.val))

theorem sixthPowerAmplifierPart_outsideS (I : ExteriorIdeal K S) :
    ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ (sixthPowerAmplifierPart I.val).val → p ∉ S := by
  intro p hp
  exact I.property p (dvd_trans hp (sixthPowerAmplifierPart_dvd I.val))

def exteriorSixthPowerFreePart (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨sixthPowerFreePart I.val, sixthPowerFreePart_outsideS S I⟩

def exteriorSixthPowerAmplifierPart (I : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨sixthPowerAmplifierPart I.val, sixthPowerAmplifierPart_outsideS S I⟩

theorem exteriorSixthPowerFree_decomposition (I : ExteriorIdeal K S) :
    (exteriorSixthPowerFreePart S I).val *
      (exteriorSixthPowerAmplifierPart S I).val ^ 6 = I.val :=
  sixthPowerFreePart_mul_amplifier_sixth I.val

end HeckeGeneral.Analysis.ConditionalMoments
