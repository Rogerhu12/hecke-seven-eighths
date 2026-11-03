import ArithmeticFrequencyRowConductor
import SexticUniformLocalConductor
import Mathlib.Data.Finsupp.Order

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake invocation.

Norm comparison for the GENUINE finite conductor of the actual arithmetic
row character. The fixed S contribution is constructed from the uniform
local bound, chosen before ProbeData, row, representative or character.
The radical below is literally mathlib Ideal.radical, with a nonzero proof.
No conductor comparison, bounded S contribution or ramification is assumed.

This depends on the preceding UNCOMPILED arithmetic/CFT row candidates and
SexticUniformLocalConductor. Older candidates are frozen and unchanged.
All unit-ideal sectors remain; S behavior is bounded rather than erased.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Arithmetic.ConductorNormDraft

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The actual radical of a nonzero ideal, retaining its nonzero proof. -/
def nonzeroIdealRadical (I : (Ideal (𝓞 K))⁰) : (Ideal (𝓞 K))⁰ :=
  ⟨I.val.radical, mem_nonZeroDivisors_of_ne_zero (by
    intro hz
    have hzbot : I.val.radical = ⊥ := by
      simpa only [Ideal.zero_eq_bot] using hz
    have hIbot : I.val = ⊥ := le_bot_iff.mp
      ((Ideal.le_radical : I.val ≤ I.val.radical).trans (le_of_eq hzbot))
    exact nonZeroDivisors.coe_ne_zero I (by
      simpa only [Ideal.zero_eq_bot] using hIbot))⟩

@[simp] theorem nonzeroIdealRadical_val (I : (Ideal (𝓞 K))⁰) :
    (nonzeroIdealRadical K I).val = I.val.radical := rfl

/-- Pointwise exponent domination gives actual integral-ideal divisibility.
The quotient is constructed from the nonnegative difference of exponents. -/
theorem nonzeroIdeal_dvd_of_primeExponents_le
    (I J : (Ideal (𝓞 K))⁰) (h : primeExponents I ≤ primeExponents J) :
    I.val ∣ J.val := by
  have he : primeExponents J =
      primeExponents I + (primeExponents J - primeExponents I) :=
    (add_tsub_cancel_of_le h).symm
  refine ⟨(idealOfPrimeExponents (primeExponents J - primeExponents I)).val, ?_⟩
  calc
    J.val = (idealOfPrimeExponents (primeExponents J)).val := by
      rw [idealOfPrimeExponents_primeExponents]
    _ = (idealOfPrimeExponents
        (primeExponents I + (primeExponents J - primeExponents I))).val :=
      congrArg (fun e : HeightOneSpectrum (𝓞 K) →₀ ℕ =>
        (idealOfPrimeExponents e).val) he
    _ = I.val *
        (idealOfPrimeExponents (primeExponents J - primeExponents I)).val := by
      rw [idealOfPrimeExponents_add, idealOfPrimeExponents_primeExponents]
      rfl

theorem absNorm_le_of_primeExponents_le
    (I J : (Ideal (𝓞 K))⁰) (h : primeExponents I ≤ primeExponents J) :
    I.val.absNorm ≤ J.val.absNorm :=
  Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors J)
    (map_dvd Ideal.absNorm (nonzeroIdeal_dvd_of_primeExponents_le K I J h))

/-- Every prime occurring in I also occurs in its genuine radical. For the
conductor comparison only this positive lower bound is needed. -/
theorem primeExponents_nonzeroIdealRadical_pos
    (I : (Ideal (𝓞 K))⁰) (p : HeightOneSpectrum (𝓞 K))
    (hp : 0 < primeExponents I p) :
    0 < primeExponents (nonzeroIdealRadical K I) p := by
  have hm : idealPrimeMultiplicity K p I.val ≠ 0 := by
    rw [idealPrimeMultiplicity_eq_primeExponents K I p]
    exact Nat.ne_of_gt hp
  have hdiv : p.asIdeal ∣ I.val :=
    (Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero I) p.irreducible).mp hm
  have hle : I.val ≤ p.asIdeal := Ideal.dvd_iff_le.mp hdiv
  have hrad : I.val.radical ≤ p.asIdeal := p.isPrime.radical_le_iff.mpr hle
  have hdivrad : p.asIdeal ∣ (nonzeroIdealRadical K I).val :=
    Ideal.dvd_iff_le.mpr hrad
  have hmrad : idealPrimeMultiplicity K p (nonzeroIdealRadical K I).val ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero (nonzeroIdealRadical K I)) p.irreducible).mpr hdivrad
  rw [idealPrimeMultiplicity_eq_primeExponents K (nonzeroIdealRadical K I) p] at hmrad
  exact Nat.pos_of_ne_zero hmrad

/-- The genuine radical has no larger norm than the original ideal. -/
theorem absNorm_nonzeroIdealRadical_le (I : (Ideal (𝓞 K))⁰) :
    (nonzeroIdealRadical K I).val.absNorm ≤ I.val.absNorm :=
  Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I)
    (Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.le_radical : I.val ≤ I.val.radical))

/-- Choose a depth from the LOCAL FIELD theorem, before any character. -/
def sexticUniformLocalDepth (p : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Classical.choose (exists_uniform_localConductorExponent_bound_pow_six K p)

theorem sexticUniformLocalDepth_pos (p : HeightOneSpectrum (𝓞 K)) :
    0 < sexticUniformLocalDepth K p :=
  (Classical.choose_spec (exists_uniform_localConductorExponent_bound_pow_six K p)).1

theorem localConductorExponent_le_sexticUniformLocalDepth
    (p : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K) (hχ : χ ^ 6 = 1) :
    localConductorExponent K χ p ≤ sexticUniformLocalDepth K p :=
  (Classical.choose_spec (exists_uniform_localConductorExponent_bound_pow_six K p)).2 χ hχ

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A genuinely finitely supported exponent budget on the ORIGINAL S. -/
def sexticSPrimeExponentBudget : HeightOneSpectrum (𝓞 K) →₀ ℕ :=
  Finsupp.onFinset S.toFinset
    (fun p => if p ∈ S then sexticUniformLocalDepth K p else 0) (by
      intro p hp
      apply Set.mem_toFinset.mpr
      by_contra hnot
      exact hp (if_neg hnot))

@[simp] theorem sexticSPrimeExponentBudget_apply (p : HeightOneSpectrum (𝓞 K)) :
    sexticSPrimeExponentBudget K S p =
      if p ∈ S then sexticUniformLocalDepth K p else 0 := rfl

def sexticSConductorBudgetIdeal : (Ideal (𝓞 K))⁰ :=
  idealOfPrimeExponents (sexticSPrimeExponentBudget K S)

/-- A fixed natural constant depending only on K and the original finite S. -/
def sexticSConductorNormConstant : ℕ :=
  (sexticSConductorBudgetIdeal K S).val.absNorm

theorem sexticSConductorNormConstant_pos : 0 < sexticSConductorNormConstant K S :=
  Ideal.absNorm_pos_of_nonZeroDivisors (sexticSConductorBudgetIdeal K S)

end HeckeGeneral.Arithmetic.ConductorNormDraft

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.ConductorNormDraft
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Actual ideal divisibility, derived from the constructed S budget and
the exact outside-S conductor theorem. No conductor hypothesis is input. -/
theorem arithmeticRowCharacter_finiteConductor_dvd_SBudget_mul_radical
    (P : ProbeData K S) (v : FrequencyRow K S) :
    (finiteConductor K (arithmeticRowCharacter K S P v)).val ∣
      (sexticSConductorBudgetIdeal K S * nonzeroIdealRadical K v.ideal.val).val := by
  apply nonzeroIdeal_dvd_of_primeExponents_le K
  intro p
  rw [primeExponents_mul, Finsupp.add_apply]
  rw [sexticSConductorBudgetIdeal, primeExponents_idealOfPrimeExponents,
    sexticSPrimeExponentBudget_apply]
  by_cases hp : p ∈ S
  · rw [if_pos hp, primeExponents_finiteConductor, conductorExponents_apply]
    exact (localConductorExponent_le_sexticUniformLocalDepth K p
      (arithmeticRowCharacter K S P v)
      (arithmeticRowCharacter_pow_six_eq_one K S P v)).trans (Nat.le_add_right _ _)
  · rw [if_neg hp, zero_add,
      arithmeticRowCharacter_finiteConductor_primeExponents_outside_S K S P v p hp]
    by_cases hz : primeExponents v.ideal.val p = 0
    · simp only [if_pos hz]
      exact Nat.zero_le _
    · rw [if_neg hz]
      exact Nat.succ_le_of_lt (primeExponents_nonzeroIdealRadical_pos K v.ideal.val p
        (Nat.pos_of_ne_zero hz))

/-- The genuine finite conductor norm is bounded by a fixed S constant
times the norm of the ORIGINAL row ideal's genuine radical. -/
theorem arithmeticRowCharacter_finiteConductor_absNorm_le_radical
    (P : ProbeData K S) (v : FrequencyRow K S) :
    (finiteConductor K (arithmeticRowCharacter K S P v)).val.absNorm ≤
      sexticSConductorNormConstant K S * v.ideal.val.val.radical.absNorm := by
  have hdiv := arithmeticRowCharacter_finiteConductor_dvd_SBudget_mul_radical K S P v
  have hn := Nat.le_of_dvd
    (Ideal.absNorm_pos_of_nonZeroDivisors
      (sexticSConductorBudgetIdeal K S * nonzeroIdealRadical K v.ideal.val))
    (map_dvd Ideal.absNorm hdiv)
  simpa only [Submonoid.coe_mul, map_mul, sexticSConductorNormConstant,
    nonzeroIdealRadical_val] using hn

/-- The second comparison uses only I ≤ radical(I). -/
theorem arithmeticRowCharacter_radical_bound_le_originalIdeal
    (v : FrequencyRow K S) :
    sexticSConductorNormConstant K S * v.ideal.val.val.radical.absNorm ≤
      sexticSConductorNormConstant K S * v.ideal.val.val.absNorm :=
  Nat.mul_le_mul_left _ (absNorm_nonzeroIdealRadical_le K v.ideal.val)

theorem arithmeticRowCharacter_finiteConductor_absNorm_le_originalIdeal
    (P : ProbeData K S) (v : FrequencyRow K S) :
    (finiteConductor K (arithmeticRowCharacter K S P v)).val.absNorm ≤
      sexticSConductorNormConstant K S * v.ideal.val.val.absNorm :=
  (arithmeticRowCharacter_finiteConductor_absNorm_le_radical K S P v).trans
    (arithmeticRowCharacter_radical_bound_le_originalIdeal K S v)

/-- The fixed constant precedes even ProbeData, and hence all actual rows,
unit sectors, characters, sixth-power representatives and heights. -/
theorem exists_fixed_arithmeticRowCharacter_conductor_absNorm_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ (P : ProbeData K S) (v : FrequencyRow K S),
      (finiteConductor K (arithmeticRowCharacter K S P v)).val.absNorm ≤
          C * v.ideal.val.val.radical.absNorm ∧
        C * v.ideal.val.val.radical.absNorm ≤ C * v.ideal.val.val.absNorm := by
  refine ⟨sexticSConductorNormConstant K S,
    sexticSConductorNormConstant_pos K S, fun P v => ?_⟩
  exact ⟨arithmeticRowCharacter_finiteConductor_absNorm_le_radical K S P v,
    arithmeticRowCharacter_radical_bound_le_originalIdeal K S v⟩

end HeckeGeneral.ThetaSkeleton.Physical
