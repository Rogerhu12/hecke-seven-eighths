import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionMask
import HeckeSkeleton.HeckeConductorNorm
import ArithmeticFrequencyRowConductorNorm
import RowCharacterCanonicalUniqueness

/-!
# The actual conductor and the remaining deletion product

Primes in the genuine finite conductor already have zero Hecke
coefficients, so they are removed from the explicit deletion set by an
identity of coefficient functions.  The remaining squarefree product is
coprime to the conductor.  Their product divides a constructed modulus:
the fixed background conductor, the proved sextic S-wild budget, the
fixed S/6 mask, the original complete row ideal, and the remaining ideal.

Thus the reflected scale is linear in the full row norm and remaining
ideal norm.  It is not estimated by multiplying two independent row-norm
bounds, and no conductor comparison is supplied as an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

private theorem primeCoefficient_zero_of_conductor_dvd
    (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ (finiteConductor K χ).val) : primeCoefficient K χ p = 0 := by
  apply primeCoefficient_of_ramified
  intro hunramified
  have hz : primeExponents (finiteConductor K χ) p = 0 := by
    rw [primeExponents_finiteConductor, conductorExponents_apply]
    exact (localConductorExponent_eq_zero_iff K χ p).mpr hunramified
  have hm : p.asIdeal ∈ normalizedFactors (finiteConductor K χ).val :=
    (Ideal.mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero (finiteConductor K χ))).mpr
      ⟨p.isPrime, Ideal.dvd_iff_le.mp hp⟩
  have hpos : 0 < primeExponents (finiteConductor K χ) p :=
    Multiset.count_pos.mpr hm
  omega

/-- A prime of the actual finite conductor forces the actual ideal
coefficient to vanish, with no separate primitivity hypothesis. -/
theorem heckeCoefficient_zero_of_conductor_prime (χ : HeckeCharacter K)
    (P I : Ideal (𝓞 K)) (hP : Prime P)
    (hPC : P ∣ (finiteConductor K χ).val) (hPI : P ∣ I) :
    idealCoefficient (primeCoefficient K χ) I = 0 := by
  let p : HeightOneSpectrum (𝓞 K) := HeightOneSpectrum.ofPrime hP
  obtain ⟨J, hJ⟩ := hPI
  rw [hJ, idealCoefficient_mul]
  have hp : idealCoefficient (primeCoefficient K χ) P = 0 := by
    change idealCoefficient (primeCoefficient K χ) p.asIdeal = 0
    rw [idealCoefficient_prime]
    exact primeCoefficient_zero_of_conductor_dvd χ p hPC
  rw [hp, zero_mul]

/-- Exact pruning of conductor primes from an arbitrary finite deletion
set. The original coefficient is unchanged at every integral ideal. -/
theorem excl_heckeCoefficient_conductor_sdiff (χ : HeckeCharacter K)
    (P : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) :
    excl P (idealCoefficient (primeCoefficient K χ)) I =
      excl (P \ primeSupport (finiteConductor K χ).val)
        (idealCoefficient (primeCoefficient K χ)) I := by
  by_cases ho : outside P I
  · have hr : outside (P \ primeSupport (finiteConductor K χ).val) I :=
      fun Q hQ => ho Q (Finset.mem_sdiff.mp hQ).1
    simp only [excl, if_pos ho, if_pos hr]
  · by_cases hr : outside (P \ primeSupport (finiteConductor K χ).val) I
    · have hex : ∃ Q, Q ∈ P ∧ Q ∣ I := by
        by_contra hn
        apply ho
        intro Q hQP hQI
        exact hn ⟨Q, hQP, hQI⟩
      obtain ⟨Q, hQP, hQI⟩ := hex
      have hQC : Q ∈ primeSupport (finiteConductor K χ).val := by
        by_contra hn
        exact hr Q (Finset.mem_sdiff.mpr ⟨hQP, hn⟩) hQI
      have hz := heckeCoefficient_zero_of_conductor_prime χ Q I (support_prime hQC)
        ((prime_mem_support_iff _ _ (nonZeroDivisors.coe_ne_zero (finiteConductor K χ))
          (support_prime hQC)).mp hQC) hQI
      simp only [excl, if_neg ho, if_pos hr, hz]
    · simp only [excl, if_neg ho, if_neg hr]

theorem plainPoly_excl_conductor_sdiff (χ : HeckeCharacter K)
    (P : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (X : ℝ) :
    plainPoly (excl P (idealCoefficient (primeCoefficient K χ))) F X =
      plainPoly (excl (P \ primeSupport (finiteConductor K χ).val)
        (idealCoefficient (primeCoefficient K χ))) F X := by
  have h := funext (excl_heckeCoefficient_conductor_sdiff χ P)
  rw [h]

/-- The inverse character has the identical conductor.  Restoration to
the pruned set is therefore exactly restoration to the original mask. -/
theorem plainPoly_inv_restore_original_mask (χ : HeckeCharacter K)
    (P : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (X : ℝ) :
    plainPoly (excl (P \ primeSupport (finiteConductor K χ).val)
        (idealCoefficient (primeCoefficient K χ⁻¹))) F X =
      plainPoly (excl P (idealCoefficient (primeCoefficient K χ⁻¹))) F X := by
  simpa only [finiteConductor_inv] using
    (plainPoly_excl_conductor_sdiff χ⁻¹ P F X).symm

theorem plainPolynomial_eq_remaining_pruned_sum {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I R.val)))
    (N t : ℝ) :
    let χ := d.plainBackground * d.rowCharacter u
    plainPolynomial d W u N t =
      plainPoly (excl (remainingRowDeletionPrimes S u R \
        primeSupport (finiteConductor K χ).val) (idealCoefficient (primeCoefficient K χ)))
        (W.profile u t) N := by
  dsimp only
  rw [plainPolynomial_eq_remaining_deleted_sum d W S u R hmask N t,
    plainPoly_excl_conductor_sdiff]

/-- The original complete ideal still controls the conductor after its
actual sixth-power-free character representative is selected. -/
theorem completeRowCharacter_conductor_dvd
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (ξ : SixthUnitClasses K S) (u : ExteriorIdeal K S) :
    (finiteConductor K (completeIdealRowCharacter K S P R ξ u.val)).val ∣
      (sexticSConductorBudgetIdeal K S).val * u.val.val := by
  rw [completeIdealRowCharacter_exterior, rowCharacterInput_character_eq_arithmetic]
  have h := arithmeticRowCharacter_finiteConductor_dvd_SBudget_mul_radical K S P
    (decomposedFrequencyRow K S u ξ)
  have hr : (nonzeroIdealRadical K (decomposedFrequencyRow K S u ξ).ideal.val).val ∣
      u.val.val := by
    apply dvd_trans (Ideal.dvd_iff_le.mpr Ideal.le_radical)
    exact sixthPowerFreePart_dvd u.val
  exact h.trans (mul_dvd_mul (dvd_refl _) hr)

theorem plainRowCharacter_conductor_dvd
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (β : HeckeCharacter K) (ξ : SixthUnitClasses K S) (u : ExteriorIdeal K S) :
    (finiteConductor K (β * completeIdealRowCharacter K S P R ξ u.val)).val ∣
      ((finiteConductor K β).val * (sexticSConductorBudgetIdeal K S).val) * u.val.val := by
  have h := (finiteConductor_mul_dvd K β
    (completeIdealRowCharacter K S P R ξ u.val)).trans
      (mul_dvd_mul (dvd_refl _) (completeRowCharacter_conductor_dvd S P R ξ u))
  simpa only [mul_assoc] using h

/-- All fixed arithmetic costs, chosen before the complete row, unit
sector, remaining ideal and every analytic scale. -/
def reflectionConductorBudget (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (β : HeckeCharacter K) : Ideal (𝓞 K) :=
  ((finiteConductor K β).val * (sexticSConductorBudgetIdeal K S).val) *
    fixedRowDeletionIdeal S

theorem reflectionConductorBudget_ne_bot
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (β : HeckeCharacter K) :
    reflectionConductorBudget S β ≠ ⊥ :=
  mul_ne_zero (mul_ne_zero (nonZeroDivisors.coe_ne_zero (finiteConductor K β))
    (nonZeroDivisors.coe_ne_zero (sexticSConductorBudgetIdeal K S)))
    (fixedRowDeletionIdeal_ne_bot S)

/-- The conductor and only the genuinely redundant deletion primes fit
in one modulus. This is the essential linear row-norm budget. -/
theorem actualConductor_remainingProduct_dvd
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (β : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K) :
    let χ := β * completeIdealRowCharacter K S P R ξ u.val
    let E := remainingRowDeletionPrimes S u.val extra \ primeSupport (finiteConductor K χ).val
    (finiteConductor K χ).val * (∏ p ∈ E, p) ∣
      reflectionConductorBudget S β * u.val.val * extra.val := by
  dsimp only
  let χ := β * completeIdealRowCharacter K S P R ξ u.val
  let E := remainingRowDeletionPrimes S u.val extra \ primeSupport (finiteConductor K χ).val
  let M := reflectionConductorBudget S β * u.val.val * extra.val
  have hC0 : (finiteConductor K χ).val ≠ ⊥ :=
    nonZeroDivisors.coe_ne_zero (finiteConductor K χ)
  have hM0 : M ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (reflectionConductorBudget_ne_bot S β) (nonZeroDivisors.coe_ne_zero u.val))
    (nonZeroDivisors.coe_ne_zero extra)
  have hE : ∀ p ∈ E, Prime p := fun p hp =>
    remainingRowDeletionPrimes_prime S u.val extra p (Finset.mem_sdiff.mp hp).1
  have hC : (finiteConductor K χ).val ∣ M := by
    apply (plainRowCharacter_conductor_dvd S P R β ξ u).trans
    refine ⟨fixedRowDeletionIdeal S * extra.val, ?_⟩
    dsimp only [M, reflectionConductorBudget]
    ring
  have hbase : fixedRowDeletionIdeal S * u.val.val * extra.val ∣ M := by
    have h := dvd_mul_of_dvd_right
      (dvd_refl (fixedRowDeletionIdeal S * u.val.val * extra.val))
      ((finiteConductor K β).val * (sexticSConductorBudgetIdeal K S).val)
    simpa only [M, reflectionConductorBudget, mul_assoc] using h
  have hD : (∏ p ∈ E, p) ∣ M := by
    apply support_product_dvd hM0
    intro p hp
    apply (prime_mem_support_iff M p hM0 (hE p hp)).mpr
    have hprime : p ∣ ∏ q ∈ remainingRowDeletionPrimes S u.val extra, q :=
      Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.mp hp).1
    exact hprime.trans ((remainingRowDeletionProduct_dvd S u.val extra).trans hbase)
  have hcoprime : IsCoprime (∏ p ∈ E, p) (finiteConductor K χ).val := by
    apply (primeSupport_disjoint_iff (subset_product_nonzero E hE) hC0).mp
    have hf : normalizedFactors (∏ p ∈ E, p) = E.val := by
      simpa using normalizedFactors_prod_of_prime (m := E.val) hE
    have hs : primeSupport (∏ p ∈ E, p) = E := by
      simp only [primeSupport, hf, Finset.val_toFinset]
    rw [hs]
    exact Finset.disjoint_left.mpr (fun p hp hpc => (Finset.mem_sdiff.mp hp).2 hpc)
  exact hcoprime.symm.mul_dvd hC hD

def reflectionConductorConstant (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (β : HeckeCharacter K) : ℝ :=
  ((NumberField.discr K).natAbs : ℝ) * (Ideal.absNorm (reflectionConductorBudget S β) : ℝ)

theorem reflectionConductorConstant_pos
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (β : HeckeCharacter K) :
    0 < reflectionConductorConstant S β := by
  apply mul_pos
  · exact Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
  · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (fun hz => reflectionConductorBudget_ne_bot S β (Ideal.absNorm_eq_zero_iff.mp hz)))

/-- One constant for all three backgrounds permitted by MomentData,
fixed before any node or row of the recursive family. -/
def uniformReflectionConductorConstant (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (ψ : HeckeCharacter K) : ℝ :=
  reflectionConductorConstant S 1 + reflectionConductorConstant S ψ +
    reflectionConductorConstant S ψ⁻¹

theorem uniformReflectionConductorConstant_pos
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (ψ : HeckeCharacter K) :
    0 < uniformReflectionConductorConstant S ψ :=
  add_pos (add_pos (reflectionConductorConstant_pos S 1)
    (reflectionConductorConstant_pos S ψ)) (reflectionConductorConstant_pos S ψ⁻¹)

theorem reflectionConductorConstant_le_uniform
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (β ψ : HeckeCharacter K)
    (hβ : β = 1 ∨ β = ψ ∨ β = ψ⁻¹) :
    reflectionConductorConstant S β ≤ uniformReflectionConductorConstant S ψ := by
  have h₀ := reflectionConductorConstant_pos S (1 : HeckeCharacter K)
  have h₁ := reflectionConductorConstant_pos S ψ
  have h₂ := reflectionConductorConstant_pos S ψ⁻¹
  rcases hβ with rfl | rfl | rfl <;>
    unfold uniformReflectionConductorConstant <;> linarith

theorem actualReflectionScale_remainingProduct_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (β : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K) :
    let χ := β * completeIdealRowCharacter K S P R ξ u.val
    let E := remainingRowDeletionPrimes S u.val extra \ primeSupport (finiteConductor K χ).val
    heckeConductorScale K χ * (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ≤
      reflectionConductorConstant S β * idealNorm K u.val * idealNorm K extra := by
  dsimp only
  have hM : reflectionConductorBudget S β * u.val.val * extra.val ≠ ⊥ :=
    mul_ne_zero (mul_ne_zero (reflectionConductorBudget_ne_bot S β)
      (nonZeroDivisors.coe_ne_zero u.val)) (nonZeroDivisors.coe_ne_zero extra)
  have h := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hM (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm (actualConductor_remainingProduct_dvd S P R β ξ u extra))
  simp only [map_mul] at h
  have hreal : ((finiteConductor K (β * completeIdealRowCharacter K S P R ξ u.val)).val.absNorm : ℝ) *
      (Ideal.absNorm (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
        primeSupport (finiteConductor K (β * completeIdealRowCharacter K S P R ξ u.val)).val, p) : ℝ) ≤
        (Ideal.absNorm (reflectionConductorBudget S β) : ℝ) *
          idealNorm K u.val * idealNorm K extra := by
    dsimp only [idealNorm]
    exact_mod_cast h
  have hd : 0 ≤ ((NumberField.discr K).natAbs : ℝ) := Nat.cast_nonneg _
  simpa only [heckeConductorScale, reflectionConductorConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left hreal hd

/-- Every actual D/H descendant has the expected upper reflected scale,
with its complete remaining mask and original complete row norm. -/
theorem actual_reflectedScale_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (β : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K)
    (D : Finset (Ideal (𝓞 K)))
    (hD : D ⊆ remainingRowDeletionPrimes S u.val extra \
      primeSupport (finiteConductor K (β * completeIdealRowCharacter K S P R ξ u.val)).val)
    (H : HeckePort.Moments.NI K) (X : ℝ) (hX : 0 < X) :
    heckeConductorScale K (β * completeIdealRowCharacter K S P R ξ u.val) *
        (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / (X * inorm H) ≤
      reflectionConductorConstant S β * idealNorm K u.val * idealNorm K extra / X := by
  let χ := β * completeIdealRowCharacter K S P R ξ u.val
  let E := remainingRowDeletionPrimes S u.val extra \ primeSupport (finiteConductor K χ).val
  have hE : ∀ p ∈ E, Prime p := fun p hp =>
    remainingRowDeletionPrimes_prime S u.val extra p (Finset.mem_sdiff.mp hp).1
  have hE0 := subset_product_nonzero E hE
  have hsupport : primeSupport (∏ p ∈ E, p) = E := by
    have hf : normalizedFactors (∏ p ∈ E, p) = E.val := by
      simpa using normalizedFactors_prod_of_prime (m := E.val) hE
    simp only [primeSupport, hf, Finset.val_toFinset]
  have hdiv : (∏ p ∈ D, p) ∣ ∏ p ∈ E, p := by
    apply support_product_dvd hE0
    simpa only [hsupport] using hD
  have hnorm : (Ideal.absNorm (∏ p ∈ D, p) : ℝ) ≤
      (Ideal.absNorm (∏ p ∈ E, p) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (fun hz => hE0 (Ideal.absNorm_eq_zero_iff.mp hz)))
      (map_dvd Ideal.absNorm hdiv)
  have hQ := conductorScale_pos K χ
  have hbound : heckeConductorScale K χ * (Ideal.absNorm (∏ p ∈ D, p) : ℝ) ≤
      reflectionConductorConstant S β * idealNorm K u.val * idealNorm K extra :=
    (mul_le_mul_of_nonneg_left hnorm hQ.le).trans
      (actualReflectionScale_remainingProduct_le S P R β ξ u extra)
  have hH : 1 ≤ inorm H := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => H.property (Ideal.absNorm_eq_zero_iff.mp hz)))
  calc
    _ = (heckeConductorScale K χ * (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / X) / inorm H := by
      rw [div_div]
    _ ≤ heckeConductorScale K χ * (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / X :=
      div_le_self (div_nonneg (mul_nonneg hQ.le (Nat.cast_nonneg _)) hX.le) hH
    _ ≤ _ := div_le_div_of_nonneg_right hbound hX.le

end HeckeSkeleton.Moments.EngineInduction
