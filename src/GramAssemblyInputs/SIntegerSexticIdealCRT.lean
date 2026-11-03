import SIntegerSexticPrimePowerQuotient
import FiniteAffineCorrelationProduct
import HeckeGeneral.Arithmetic.IdealFactorization
import HeckeGeneral.Arithmetic.SIntegerModulusCRT
import HeckeGeneral.Characters.ConductorCRT

/-! SOURCE ONLY, UNCOMPILED.

The index set and exponents below are extracted from the actual nonzero
ordinary ideal. The CRT is Mathlib's Chinese remainder equivalence for
the extended prime-power ideals, not a supplied abstract equivalence.
Its coordinates are the literal quotient maps on every S-integer.
-/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors Function

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)

/-- The sextic symbol's Associates count is the actual ideal factorization
exponent already used by `primeExponentEquiv`. -/
theorem idealPrimeMultiplicity_eq_primeExponents (p : HeightOneSpectrum (𝓞 K)) :
    idealPrimeMultiplicity K p I =
      primeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ p := by
  unfold idealPrimeMultiplicity
  exact (Ideal.count_associates_factors_eq hI p.isPrime p.ne_bot).trans
    (primeExponents_apply ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ p).symm

def sexticIdealPrimeExponents : HeightOneSpectrum (𝓞 K) →₀ ℕ :=
  primeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

@[simp] theorem sexticIdealPrimeExponents_apply (p : HeightOneSpectrum (𝓞 K)) :
    sexticIdealPrimeExponents K I hI p = idealPrimeMultiplicity K p I :=
  (idealPrimeMultiplicity_eq_primeExponents K I hI p).symm

abbrev sexticIdealPlaces := (sexticIdealPrimeExponents K I hI).support

theorem mem_sexticIdealPlaces_iff (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ sexticIdealPlaces K I hI ↔ p.asIdeal ∣ I := by
  change p ∈ (sexticIdealPrimeExponents K I hI).support ↔ p.asIdeal ∣ I
  rw [Finsupp.mem_support_iff, sexticIdealPrimeExponents_apply]
  exact Associates.count_ne_zero_iff_dvd hI p.irreducible

theorem sexticIdealPlaces_multiplicity_pos (p : sexticIdealPlaces K I hI) :
    1 ≤ idealPrimeMultiplicity K p.val I := by
  have hp := Finsupp.mem_support_iff.mp p.property
  rw [sexticIdealPrimeExponents_apply] at hp
  exact Nat.one_le_iff_ne_zero.mpr hp

theorem sexticIdeal_primePower_product :
    (∏ p : sexticIdealPlaces K I hI,
      p.val.asIdeal ^ idealPrimeMultiplicity K p.val I) = I := by
  simp_rw [← sexticIdealPrimeExponents_apply K I hI]
  calc
    _ = (idealOfPrimeExponents (sexticIdealPrimeExponents K I hI)).val :=
      Finset.prod_coe_sort (sexticIdealPrimeExponents K I hI).support
        (fun p => p.asIdeal ^ sexticIdealPrimeExponents K I hI p)
    _ = I := congrArg Subtype.val (idealOfPrimeExponents_primeExponents _)

theorem sexticIdealPlaces_not_mem
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
    (p : sexticIdealPlaces K I hI) : p.val ∉ S :=
  hS p.val ((mem_sexticIdealPlaces_iff K I hI p.val).mp p.property)

/-- Actual extended prime-power ideals; no prime quotient is treated as a field. -/
abbrev sexticIdealLocalIdeal (p : sexticIdealPlaces K I hI) : Ideal (S.integer K) :=
  (p.val.asIdeal ^ idealPrimeMultiplicity K p.val I).map
    (algebraMap (𝓞 K) (S.integer K))

theorem sexticIdealLocalIdeal_pairwise_isCoprime :
    Pairwise (IsCoprime on sexticIdealLocalIdeal K S I hI) := by
  intro p q hpq
  apply Ideal.isCoprime_iff_sup_eq.mpr
  have hpq' : p.val ≠ q.val := Subtype.val_injective.ne hpq
  rw [← Ideal.map_sup,
    (p.val.isCoprime_pow_of_ne q.val hpq'
      (idealPrimeMultiplicity K p.val I) (idealPrimeMultiplicity K q.val I)).sup_eq,
    Ideal.map_top]

theorem sexticIdealLocalIdeal_product :
    (∏ p : sexticIdealPlaces K I hI, sexticIdealLocalIdeal K S I hI p) =
      I.map (algebraMap (𝓞 K) (S.integer K)) := by
  change (∏ p : sexticIdealPlaces K I hI,
      Ideal.mapHom (algebraMap (𝓞 K) (S.integer K))
        (p.val.asIdeal ^ idealPrimeMultiplicity K p.val I)) = _
  rw [← map_prod, sexticIdeal_primePower_product K I hI]
  rfl

theorem sexticIdealLocalIdeal_iInf :
    (⨅ p : sexticIdealPlaces K I hI, sexticIdealLocalIdeal K S I hI p) =
      I.map (algebraMap (𝓞 K) (S.integer K)) := by
  have hp := Ideal.prod_eq_iInf_of_pairwise_isCoprime
    ((sexticIdealLocalIdeal_pairwise_isCoprime K S I hI).set_pairwise
      (Finset.univ : Finset (sexticIdealPlaces K I hI)))
  have hp' : (∏ p : sexticIdealPlaces K I hI, sexticIdealLocalIdeal K S I hI p) =
      ⨅ p : sexticIdealPlaces K I hI, sexticIdealLocalIdeal K S I hI p := by
    simpa only [Finset.mem_univ, iInf_true] using hp
  exact hp'.symm.trans (sexticIdealLocalIdeal_product K S I hI)

abbrev SIntegerSexticIdealLocalQuotients :=
  ∀ p : sexticIdealPlaces K I hI,
    sIntegerPrimePowerQuotient K S p.val (idealPrimeMultiplicity K p.val I)

/-- CRT for the actual ideal, including the empty product for `I = ⊤`.
Coprimality with S is only needed for the later residue-character bridge;
the CRT itself also permits extended factors that become the unit ideal. -/
def sIntegerSexticIdealCRT :
    (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) ≃+*
      SIntegerSexticIdealLocalQuotients K S I hI :=
  (Ideal.quotEquivOfEq (sexticIdealLocalIdeal_iInf K S I hI).symm).trans
    (Ideal.quotientInfRingEquivPiQuotient (sexticIdealLocalIdeal K S I hI)
      (sexticIdealLocalIdeal_pairwise_isCoprime K S I hI))

@[simp] theorem sIntegerSexticIdealCRT_mk
    (a : S.integer K) (p : sexticIdealPlaces K I hI) :
    sIntegerSexticIdealCRT K S I hI
      (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K))) a) p =
      Ideal.Quotient.mk (sexticIdealLocalIdeal K S I hI p) a := by
  unfold sIntegerSexticIdealCRT
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

/-- Each actual prime-power factor divides the original ideal. -/
theorem sexticIdealPrimePower_dvd (p : sexticIdealPlaces K I hI) :
    p.val.asIdeal ^ idealPrimeMultiplicity K p.val I ∣ I := by
  have hp : p.val.asIdeal ^ idealPrimeMultiplicity K p.val I ∣
      ∏ q : sexticIdealPlaces K I hI,
        q.val.asIdeal ^ idealPrimeMultiplicity K q.val I :=
    Finset.dvd_prod_of_mem
      (fun q : sexticIdealPlaces K I hI =>
        q.val.asIdeal ^ idealPrimeMultiplicity K q.val I) (Finset.mem_univ p)
  rwa [sexticIdeal_primePower_product K I hI] at hp

def sexticIdealPrimePowerQuotientMap (p : sexticIdealPlaces K I hI) :
    (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) →+*
      sIntegerPrimePowerQuotient K S p.val (idealPrimeMultiplicity K p.val I) :=
  Ideal.quotientMap (sexticIdealLocalIdeal K S I hI p)
    (RingHom.id (S.integer K)) (by
      simpa only [Ideal.comap_id] using
        Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K))
          (Ideal.dvd_iff_le.mp (sexticIdealPrimePower_dvd K I hI p)))

@[simp] theorem sexticIdealPrimePowerQuotientMap_mk
    (a : S.integer K) (p : sexticIdealPlaces K I hI) :
    sexticIdealPrimePowerQuotientMap K S I hI p (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (sexticIdealLocalIdeal K S I hI p) a := by
  simp only [sexticIdealPrimePowerQuotientMap, Ideal.quotientMap_mk, RingHom.id_apply]

theorem sIntegerSexticIdealCRT_apply
    (z : S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K)))
    (p : sexticIdealPlaces K I hI) :
    sIntegerSexticIdealCRT K S I hI z p =
      sexticIdealPrimePowerQuotientMap K S I hI p z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [sIntegerSexticIdealCRT_mk, sexticIdealPrimePowerQuotientMap_mk]

end HeckeGeneral.Characters
