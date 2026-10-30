import CubicSieve.CubicCharacters
import ArithmeticFrequencyRowConductorNorm
import HeckeGeneral.Characters.ConductorArithmetic

/-!
Actual finite conductor bounds and separation for the cubic Kummer family.
The contribution at the original finite S is bounded by the existing uniform
local sixth-power conductor theorem. No analytic large sieve estimate or
ray-class primitivity conclusion is assumed or asserted.
-/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.CubicConductors

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.CubicCharacters
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

private theorem exterior_exponent_zero (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) : primeExponents J.val p = 0 := by
  by_contra hz
  have hm : AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity
      K p J.val.val ≠ 0 := by
    rw [HeckeGeneral.Analysis.PrimeCalibrationDraft.idealPrimeMultiplicity_eq_primeExponents]
    exact hz
  have hdiv : p.asIdeal ∣ J.val.val := by
    exact (Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero J.val) p.irreducible).mp hm
  exact J.property p hdiv hp

omit [Fintype S] in
private theorem squarefree_exponent (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents J.val p = if p.asIdeal ∣ J.val.val then 1 else 0 := by
  have hle : primeExponents J.val p ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors
        (nonZeroDivisors.coe_ne_zero J.val)).mp hJ) p.asIdeal
  have hiff : primeExponents J.val p ≠ 0 ↔ p.asIdeal ∣ J.val.val := by
    rw [← HeckeGeneral.Analysis.PrimeCalibrationDraft.idealPrimeMultiplicity_eq_primeExponents
      K J.val p]
    exact Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero J.val) p.irreducible
  by_cases hdiv : p.asIdeal ∣ J.val.val
  · rw [ite_eq_left hdiv]
    have hn := hiff.mpr hdiv
    omega
  · rw [ite_eq_right hdiv]
    by_contra hz
    exact hdiv (hiff.mp hz)

/-- Exact conductor multiplicity at every exterior prime. -/
theorem conductor_exponent_outside_S (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    localConductorExponent K (cubicCharacter K S D J) p = primeExponents J.val p := by
  rw [cubicCharacter_localConductorExponent K S D J hJ p hp,
    squarefree_exponent K S J hJ p]

/-- The actual finite conductor with its S part removed is exactly J. -/
theorem conductor_outside_S (J : ExteriorIdeal K S) (hJ : Squarefree J.val.val) :
    outsideSIdeal K S (finiteConductor K (cubicCharacter K S D J)) = J.val := by
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  ext p
  change primeExponents (outsideSIdeal K S
    (finiteConductor K (cubicCharacter K S D J))) p = primeExponents J.val p
  rw [outsideSIdeal, primeExponents_idealOfPrimeExponents, outsideSPrimeExponents]
  by_cases hp : p ∈ S
  · rw [Finsupp.filter_apply_neg (fun p => p ∉ S) _ (not_not.mpr hp),
      exterior_exponent_zero K S J p hp]
  · rw [Finsupp.filter_apply_pos (fun p => p ∉ S) _ hp,
      primeExponents_finiteConductor, conductorExponents_apply]
    exact conductor_exponent_outside_S K S D J hJ p hp

/-- A global ideal divisibility with a fixed, genuinely constructed S budget. -/
theorem conductor_dvd_budget_mul (J : ExteriorIdeal K S) (hJ : Squarefree J.val.val) :
    (finiteConductor K (cubicCharacter K S D J)).val ∣
      (sexticSConductorBudgetIdeal K S * J.val).val := by
  apply nonzeroIdeal_dvd_of_primeExponents_le K
  intro p
  rw [primeExponents_mul, Finsupp.add_apply, sexticSConductorBudgetIdeal,
    primeExponents_idealOfPrimeExponents, sexticSPrimeExponentBudget_apply,
    primeExponents_finiteConductor, conductorExponents_apply]
  by_cases hp : p ∈ S
  · rw [ite_eq_left hp]
    have h6 : cubicCharacter K S D J ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul, cubicCharacter_pow_three, one_pow]
    exact (localConductorExponent_le_sexticUniformLocalDepth K p
      (cubicCharacter K S D J) h6).trans (Nat.le_add_right _ _)
  · rw [ite_eq_right hp, zero_add, conductor_exponent_outside_S K S D J hJ p hp]

theorem conductor_absNorm_le (J : ExteriorIdeal K S) (hJ : Squarefree J.val.val) :
    (finiteConductor K (cubicCharacter K S D J)).val.absNorm ≤
      sexticSConductorNormConstant K S * J.val.val.absNorm := by
  have hdiv := conductor_dvd_budget_mul K S D J hJ
  have hn := Nat.le_of_dvd
    (Ideal.absNorm_pos_of_nonZeroDivisors (sexticSConductorBudgetIdeal K S * J.val))
    (map_dvd Ideal.absNorm hdiv)
  simpa only [Submonoid.coe_mul, map_mul, sexticSConductorNormConstant] using hn

theorem conductor_norm_le (J : ExteriorIdeal K S) (hJ : Squarefree J.val.val) :
    ((finiteConductor K (cubicCharacter K S D J)).val.absNorm : ℝ) ≤
      (sexticSConductorNormConstant K S : ℝ) * exteriorNorm K S J := by
  change ((finiteConductor K (cubicCharacter K S D J)).val.absNorm : ℝ) ≤
    (sexticSConductorNormConstant K S : ℝ) * (J.val.val.absNorm : ℝ)
  exact_mod_cast conductor_absNorm_le K S D J hJ

/-- The constant depends only on K and the original S, before D or J. -/
theorem exists_fixed_conductor_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ThetaArithmeticData K S) (J : ExteriorIdeal K S),
      Squarefree J.val.val →
        ((finiteConductor K (cubicCharacter K S E J)).val.absNorm : ℝ) ≤
          C * exteriorNorm K S J := by
  refine ⟨(sexticSConductorNormConstant K S : ℝ), ?_, fun E J hJ => ?_⟩
  · exact_mod_cast sexticSConductorNormConstant_pos K S
  · exact conductor_norm_le K S E J hJ

/-- Equal actual conductors already recover the squarefree exterior parameter. -/
theorem ideal_eq_of_conductor_eq (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)
    (h : finiteConductor K (cubicCharacter K S D I) =
      finiteConductor K (cubicCharacter K S D J)) : I = J := by
  apply Subtype.ext
  rw [← conductor_outside_S K S D I hI, ← conductor_outside_S K S D J hJ, h]

theorem ideal_eq_of_character_eq (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)
    (h : cubicCharacter K S D I = cubicCharacter K S D J) : I = J := by
  apply ideal_eq_of_conductor_eq K S D I J hI hJ
  rw [h]

theorem character_injective_squarefree : Function.Injective
    (fun J : {J : ExteriorIdeal K S // Squarefree J.val.val} =>
      cubicCharacter K S D J.val) := by
  intro I J h
  exact Subtype.ext (ideal_eq_of_character_eq K S D I.val J.val I.property J.property h)

private theorem exists_different_exterior_exponent (I J : ExteriorIdeal K S) (hne : I ≠ J) :
    ∃ p : HeightOneSpectrum (𝓞 K), p ∉ S ∧
      primeExponents I.val p ≠ primeExponents J.val p := by
  by_contra hno
  push Not at hno
  apply hne
  apply Subtype.ext
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  ext p
  change primeExponents I.val p = primeExponents J.val p
  by_cases hp : p ∈ S
  · rw [exterior_exponent_zero K S I p hp, exterior_exponent_zero K S J p hp]
  · exact hno p hp

/-- Distinct squarefree parameters give a genuinely ramified character ratio.
This is a separation statement, not a product-primitivity theorem. -/
theorem ratio_has_exterior_conductor_one (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val) (hne : I ≠ J) :
    ∃ p : HeightOneSpectrum (𝓞 K), p ∉ S ∧
      localConductorExponent K
        (cubicCharacter K S D I * (cubicCharacter K S D J)⁻¹) p = 1 := by
  obtain ⟨p, hp, hexp⟩ := exists_different_exterior_exponent K S I J hne
  refine ⟨p, hp, ?_⟩
  have hdepth : localConductorExponent K (cubicCharacter K S D I) p ≠
      localConductorExponent K (cubicCharacter K S D J)⁻¹ p := by
    rw [localConductorExponent_inv, conductor_exponent_outside_S K S D I hI p hp,
      conductor_exponent_outside_S K S D J hJ p hp]
    exact hexp
  rw [localConductorExponent_mul_eq_max_of_ne K _ _ p hdepth,
    localConductorExponent_inv, conductor_exponent_outside_S K S D I hI p hp,
    conductor_exponent_outside_S K S D J hJ p hp]
  have hi := squarefree_exponent K S I hI p
  have hj := squarefree_exponent K S J hJ p
  split_ifs at hi hj <;> omega

theorem ratio_ne_one (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val) (hne : I ≠ J) :
    cubicCharacter K S D I * (cubicCharacter K S D J)⁻¹ ≠ 1 := by
  obtain ⟨p, _, hcond⟩ := ratio_has_exterior_conductor_one K S D I J hI hJ hne
  intro h
  rw [h, localConductorExponent_one] at hcond
  omega

theorem ratio_not_normTwist (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val) (hne : I ≠ J) (t : ℝ) :
    cubicCharacter K S D I * (cubicCharacter K S D J)⁻¹ ≠ heckeNormTwist K t := by
  obtain ⟨p, _, hcond⟩ := ratio_has_exterior_conductor_one K S D I J hI hJ hne
  intro h
  rw [h, localConductorExponent_normTwist] at hcond
  omega

end CubicSieve.CubicConductors
