import HeckeGeneral.Analysis.SixthPowerFreeDecomposition
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.IdealAmplifierSmallPower

/-!
UNCOMPILED candidate. Count the actual nonzero integral ideals J whose
prime exponents outside the actual support of C are divisible by six.
The map J -> (sixthPowerFreePart J, sixthPowerAmplifierPart J) is the
already proved arithmetic decomposition. No counting or prime-distribution
hypothesis is supplied. This is the exceptional-ideal counting step of
revised Proposition 3.8; it does not yet identify physical frequency
orbits with ideals and unit sectors, or prove the weighted Gram estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.ActualGramExceptionalCountDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The manuscript's exceptional condition on actual ideal valuations. -/
def ExceptionalSixthIdeal (C J : NonzeroIdeal K) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p ∉ idealPrimeSupport K C →
    6 ∣ primeExponents J p

/-- Actual sixth-power-free ideals supported on the specified ideal C. -/
abbrev SupportedSixthBase (C : NonzeroIdeal K) :=
  {I : NonzeroIdeal K // SixthPowerFreeIdeal I ∧
    ∀ p : HeightOneSpectrum (𝓞 K), p ∉ idealPrimeSupport K C → primeExponents I p = 0}

def supportedSixthCoordinates (C : NonzeroIdeal K) (I : SupportedSixthBase K C) :
    (idealPrimeSupport K C) → Fin 6 :=
  fun p => ⟨primeExponents I.val p.val,
    (sixthPowerFreeIdeal_iff_primeExponents_lt I.val).mp I.property.1 p.val⟩

theorem supportedSixthCoordinates_injective (C : NonzeroIdeal K) :
    Function.Injective (supportedSixthCoordinates K C) := by
  intro I J h
  apply Subtype.ext
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  apply Finsupp.ext
  intro p
  by_cases hp : p ∈ idealPrimeSupport K C
  · exact congrArg Fin.val (congrFun h ⟨p, hp⟩)
  · exact (I.property.2 p hp).trans (J.property.2 p hp).symm

instance finite_supportedSixthBase (C : NonzeroIdeal K) : Finite (SupportedSixthBase K C) :=
  Finite.of_injective (supportedSixthCoordinates K C) (supportedSixthCoordinates_injective K C)

/-- Each genuine supported base is determined by one of six exponents at
each prime of C. This also handles C = 1. -/
theorem card_supportedSixthBase_le (C : NonzeroIdeal K) :
    Nat.card (SupportedSixthBase K C) ≤ 6 ^ (idealPrimeSupport K C).card := by
  have h := Nat.card_le_card_of_injective
    (supportedSixthCoordinates K C) (supportedSixthCoordinates_injective K C)
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe,
    Fintype.card_fun, Fintype.card_fin] using h

def exceptionalSupportedBase (C J : NonzeroIdeal K) (hJ : ExceptionalSixthIdeal K C J) :
    SupportedSixthBase K C :=
  ⟨sixthPowerFreePart J, sixthPowerFreePart_isSixthPowerFree J, by
    intro p hp
    rw [primeExponents_sixthPowerFreePart]
    exact Nat.mod_eq_zero_of_dvd (hJ p hp)⟩

/-- Taking a sixth root of the actual norm costs no base-norm factor,
since every nonzero integral ideal has norm at least one. -/
theorem sixthPowerAmplifier_norm_le {X : ℝ} (hX : 0 ≤ X)
    (J : NonzeroIdeal K) (hJ : idealNorm K J ≤ X) :
    idealNorm K (sixthPowerAmplifierPart J) ≤ X ^ (1 / 6 : ℝ) := by
  have hA : 0 ≤ idealNorm K (sixthPowerAmplifierPart J) := (idealNorm_pos K _).le
  have hpow : idealNorm K (sixthPowerAmplifierPart J) ^ 6 ≤ X := by
    apply le_trans _ hJ
    rw [idealNorm_sixthPowerFree_decomposition J]
    exact le_mul_of_one_le_left (pow_nonneg hA _) (one_le_idealNorm K _)
  have h := (Real.le_rpow_inv_iff_of_pos hA hX (by norm_num : (0 : ℝ) < 6)).mpr
    (by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hpow)
  simpa only [one_div] using h

def exceptionalIdealCutoff (C : NonzeroIdeal K) (X : ℝ) : Finset (NonzeroIdeal K) :=
  (dyadicIdealSupport K (X / 2)).filter (ExceptionalSixthIdeal K C)

theorem mem_exceptionalIdealCutoff {C J : NonzeroIdeal K} {X : ℝ} (hX : 0 ≤ X) :
    J ∈ exceptionalIdealCutoff K C X ↔ idealNorm K J ≤ X ∧ ExceptionalSixthIdeal K C J := by
  rw [exceptionalIdealCutoff, Finset.mem_filter,
    mem_dyadicIdealSupport_iff K (div_nonneg hX (by norm_num))]
  rw [show 2 * (X / 2) = X by ring]

/-- The finite count uses the actual arithmetic decomposition, not a
postulated parametrization or a surjective list with unproved coverage. -/
theorem exceptionalIdealCutoff_card_le (C : NonzeroIdeal K) {X : ℝ} (hX : 0 ≤ X) :
    (exceptionalIdealCutoff K C X).card ≤
      6 ^ (idealPrimeSupport K C).card *
        (dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)).card := by
  let f : {J : NonzeroIdeal K // J ∈ exceptionalIdealCutoff K C X} →
      SupportedSixthBase K C ×
        {A : NonzeroIdeal K // A ∈ dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)} :=
    fun J => (exceptionalSupportedBase K C J.val
      ((mem_exceptionalIdealCutoff K hX).mp J.property).2,
      ⟨sixthPowerAmplifierPart J.val, by
        apply (mem_dyadicIdealSupport_iff K (by positivity) _).mpr
        rw [show 2 * (X ^ (1 / 6 : ℝ) / 2) = X ^ (1 / 6 : ℝ) by ring]
        exact sixthPowerAmplifier_norm_le K hX J.val
          ((mem_exceptionalIdealCutoff K hX).mp J.property).1⟩)
  have hf : Function.Injective f := by
    intro I J h
    have hb : sixthPowerFreePart I.val = sixthPowerFreePart J.val :=
      congrArg (fun x => x.1.val) h
    have ha : sixthPowerAmplifierPart I.val = sixthPowerAmplifierPart J.val :=
      congrArg (fun x => x.2.val) h
    apply Subtype.ext
    calc
      I.val = sixthPowerFreePart I.val * sixthPowerAmplifierPart I.val ^ 6 :=
        (sixthPowerFreePart_mul_amplifier_sixth I.val).symm
      _ = sixthPowerFreePart J.val * sixthPowerAmplifierPart J.val ^ 6 := by rw [hb, ha]
      _ = J.val := sixthPowerFreePart_mul_amplifier_sixth J.val
  have hcard := Nat.card_le_card_of_injective f hf
  have hbase := card_supportedSixthBase_le K C
  have hfirst : (exceptionalIdealCutoff K C X).card ≤
      Nat.card (SupportedSixthBase K C) *
        (dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)).card := by
    simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe,
    Fintype.card_fun, Fintype.card_fin] using hcard
  exact hfirst.trans (Nat.mul_le_mul_right _ hbase)

/-- A single K-dependent constant works for every C and every X >= 1. -/
theorem exceptionalIdealCutoff_sixth_root_count :
    ∃ A : ℝ, 0 < A ∧ ∀ (C : NonzeroIdeal K) (X : ℝ), 1 ≤ X →
      ((exceptionalIdealCutoff K C X).card : ℝ) ≤
        A * (6 : ℝ) ^ (idealPrimeSupport K C).card * X ^ (1 / 6 : ℝ) := by
  obtain ⟨A, hA, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨A, hA, fun C X hX => ?_⟩
  have hr : 1 ≤ X ^ (1 / 6 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hc : ((exceptionalIdealCutoff K C X).card : ℝ) ≤
      (6 : ℝ) ^ (idealPrimeSupport K C).card *
        ((dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)).card : ℝ) := by
    exact_mod_cast exceptionalIdealCutoff_card_le K C (zero_le_one.trans hX)
  apply hc.trans
  calc
    _ ≤ (6 : ℝ) ^ (idealPrimeSupport K C).card * (A * X ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcount _ hr) (by positivity)
    _ = _ := by ring

/-- Reuse the verified two-to-the-support-cardinality bound at epsilon/3.
Cubing dominates six-to-the-cardinality and gives the exact epsilon loss. -/
theorem exists_six_pow_support_le_norm_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : NonzeroIdeal K,
      (6 : ℝ) ^ (idealPrimeSupport K C).card ≤ A * idealNorm K C ^ ε := by
  obtain ⟨A, hA, hbound⟩ := exists_two_pow_card_le_idealNorm_rpow K
    (div_pos hε (by norm_num : (0 : ℝ) < 3))
  refine ⟨A ^ 3, pow_pos hA _, fun C => ?_⟩
  let T := idealPrimeSupport K C
  have htwo : (2 : ℝ) ^ T.card ≤ A * idealNorm K C ^ (ε / 3) :=
    (hbound T).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (idealNorm_pos K _).le
        (idealNorm_squarefreeIdeal_le_of_primeSupport_subset K C T (fun _ h => h))
        (by positivity)) hA.le)
  calc
    (6 : ℝ) ^ T.card ≤ (8 : ℝ) ^ T.card := pow_le_pow_left₀ (by norm_num) (by norm_num) T.card
    _ = ((2 : ℝ) ^ T.card) ^ 3 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (A * idealNorm K C ^ (ε / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) htwo 3
    _ = A ^ 3 * idealNorm K C ^ ε := by
      have hpow : (idealNorm K C ^ (ε / 3)) ^ 3 = idealNorm K C ^ ε := by
        rw [← Real.rpow_natCast (idealNorm K C ^ (ε / 3)) 3,
          ← Real.rpow_mul (idealNorm_pos K C).le]
        congr 1
        ring
      rw [mul_pow, hpow]

/-- The actual exceptional ideal count, with the source's uniform norm
loss. Its constant is selected before both the moving C and cutoff X. -/
theorem exceptionalIdealCutoff_small_power_count {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (C : NonzeroIdeal K) (X : ℝ), 1 ≤ X →
      ((exceptionalIdealCutoff K C X).card : ℝ) ≤
        A * idealNorm K C ^ ε * X ^ (1 / 6 : ℝ) := by
  obtain ⟨B, hB, hcount⟩ := exceptionalIdealCutoff_sixth_root_count K
  obtain ⟨D, hD, hsmall⟩ := exists_six_pow_support_le_norm_rpow K hε
  refine ⟨B * D, mul_pos hB hD, fun C X hX => (hcount C X hX).trans ?_⟩
  calc
    _ ≤ B * (D * idealNorm K C ^ ε) * X ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmall C) hB.le)
        (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ = _ := by ring

end HeckeGeneral.Analysis.ActualGramExceptionalCountDraft
