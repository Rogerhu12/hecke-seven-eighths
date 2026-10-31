import SIntegerSexticIdealEvaluationFiniteSupport
import FiniteAffineCorrelationQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! Source-only, uncompiled. Actual prime-power quotient and its reduction
to the residue FIELD. The prime-power quotient is never assumed a field. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
variable (c : ℕ) (hc : 1 ≤ c)

abbrev sIntegerPrimePowerQuotient :=
  S.integer K ⧸ (p.asIdeal ^ c).map (algebraMap (𝓞 K) (S.integer K))

theorem primePower_divisor_eq (q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal ∣ p.asIdeal ^ c) : q = p := by
  have hqp : q.asIdeal ∣ p.asIdeal := q.prime.dvd_of_dvd_pow hq
  have he : p.asIdeal = q.asIdeal :=
    p.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.dvd_iff_le.mp hqp)
  exact HeightOneSpectrum.ext he.symm

def primePower_exterior : ∀ q : HeightOneSpectrum (𝓞 K),
    q.asIdeal ∣ p.asIdeal ^ c → q ∉ S := by
  intro q hq
  simpa only [primePower_divisor_eq K p c q hq] using hpS

def primePower_away_six (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) :
    ∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ p.asIdeal ^ c → (6 : 𝓞 K) ∉ q.asIdeal := by
  intro q hq
  simpa only [primePower_divisor_eq K p c q hq] using hp6

def sIntegerPrimePowerReduction :
    sIntegerPrimePowerQuotient K S p c →+* (𝓞 K ⧸ p.asIdeal) :=
  (sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hpS)).symm.toRingHom.comp
    (Ideal.quotientMap (p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)))
      (RingHom.id (S.integer K)) (by
        simpa only [Ideal.comap_id] using
          Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K)) (Ideal.pow_le_self (Nat.one_le_iff_ne_zero.mp hc))))

@[simp] theorem sIntegerPrimePowerReduction_mk (a : S.integer K) :
    sIntegerPrimePowerReduction K S p hpS c hc (Ideal.Quotient.mk _ a) =
      sIntegerSexticResidueMap K S p hpS a := by
  simp only [sIntegerPrimePowerReduction, RingHom.comp_apply, Ideal.quotientMap_mk,
    RingHom.id_apply]
  rfl

theorem sIntegerPrimePowerReduction_surjective :
    Function.Surjective (sIntegerPrimePowerReduction K S p hpS c hc) := by
  apply (sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hpS)).symm.surjective.comp
  exact Ideal.quotientMap_surjective Function.surjective_id

theorem idealPrimeMultiplicity_primePower :
    idealPrimeMultiplicity K p (p.asIdeal ^ c) = c := by
  unfold idealPrimeMultiplicity
  rw [Associates.mk_pow, Associates.count_pow
    (Associates.mk_ne_zero.mpr p.ne_bot) p.associates_irreducible,
    Associates.count_self p.associates_irreducible, mul_one]

include hpS in
theorem natCard_sIntegerPrimePowerQuotient :
    Nat.card (sIntegerPrimePowerQuotient K S p c) = Nat.card (𝓞 K ⧸ p.asIdeal) ^ c := by
  let e := sIntegerResidueEquiv K S (p.asIdeal ^ c)
    (sexticIdeal_coprime_S K S (p.asIdeal ^ c) (primePower_exterior K S p hpS c))
  rw [← Nat.card_congr e.toEquiv]
  exact cardQuot_pow_of_prime p.ne_bot

theorem natCard_sIntegerPrimePowerReduction_kernel :
    Nat.card (sIntegerPrimePowerReduction K S p hpS c hc).toAddMonoidHom.ker =
      Nat.card (𝓞 K ⧸ p.asIdeal) ^ (c - 1) := by
  letI : Finite (sIntegerPrimePowerQuotient K S p c) :=
    finite_sIntegerSexticIdealQuotient K S (p.asIdeal ^ c) (pow_ne_zero _ p.ne_bot)
      (primePower_exterior K S p hpS c)
  letI : Fintype (sIntegerPrimePowerQuotient K S p c) := Fintype.ofFinite _
  letI : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  let π := sIntegerPrimePowerReduction K S p hpS c hc
  have hcard : Nat.card (sIntegerPrimePowerQuotient K S p c) =
      Nat.card π.toAddMonoidHom.ker * Nat.card (𝓞 K ⧸ p.asIdeal) := by
    have hh := sum_comp_surjective_ringHom π
      (sIntegerPrimePowerReduction_surjective K S p hpS c hc) (fun _ => (1 : ℂ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
    rw [Nat.card_eq_fintype_card (α := sIntegerPrimePowerQuotient K S p c),
      Nat.card_eq_fintype_card (α := 𝓞 K ⧸ p.asIdeal)]
    exact_mod_cast hh
  have hq : Nat.card (𝓞 K ⧸ p.asIdeal) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  apply mul_right_cancel₀ hq
  rw [← hcard, natCard_sIntegerPrimePowerQuotient K S p hpS c]
  rw [← pow_succ, Nat.sub_add_cancel hc]

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)

/-- Literal quotient character bridge, including nonunits and zero.
The positive exponent is essential for the zero-extended MulChar power. -/
theorem sIntegerSexticPrimePowerQuotientFunction_eq_pullback
    (z : sIntegerPrimePowerQuotient K S p c) :
    sIntegerSexticIdealQuotientFunction K S ζ hζ σ (p.asIdeal ^ c)
      (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c)
      (primePower_away_six K p c hp6) z =
      (sexticResidueCharacter K ζ hζ σ p hp6 ^ c)
        (sIntegerPrimePowerReduction K S p hpS c hc z) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [sIntegerSexticIdealQuotientFunction_mk, sIntegerPrimePowerReduction_mk,
    MulChar.pow_apply' (sexticResidueCharacter K ζ hζ σ p hp6) (Nat.one_le_iff_ne_zero.mp hc)]
  have hh := sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ
    (p.asIdeal ^ c) (pow_ne_zero _ p.ne_bot)
    (primePower_exterior K S p hpS c) (primePower_away_six K p c hp6)
    {p} (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpS)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hp6)
    (by intro q hq; exact Finset.mem_singleton.mpr (primePower_divisor_eq K p c q hq)) a
  letI : Unique ↥({p} : Finset (HeightOneSpectrum (𝓞 K))) := {
    default := ⟨p, Finset.mem_singleton_self p⟩
    uniq := fun q => Subtype.ext (Finset.mem_singleton.mp q.property) }
  simpa [idealPrimeMultiplicity_primePower, sIntegerSexticEvaluation] using hh.symm

theorem sexticResidueCharacter_pow_eq_one_iff :
    sexticResidueCharacter K ζ hζ σ p hp6 ^ c = 1 ↔ 6 ∣ c := by
  rw [← orderOf_dvd_iff_pow_eq_one, sexticResidueCharacter_order K ζ hζ σ p hp6]

end HeckeGeneral.Characters
