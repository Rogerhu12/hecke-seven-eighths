import ActualSexticPeriodicLatticeWeight

/-! UNCOMPILED / native 0. Actual joint radical and full period norm bounds.
The S-depth is fixed before the moving ideals or frequencies; no radical
comparison or ideal factorization is supplied as a hypothesis. -/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramPeriodNormDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
local notation "P" => jointPlaces K C J hC hJ

/-- The right ideal has the same actual prime-power product on the union
of the two prime supports; primes absent from J contribute one. -/
theorem prod_joint_primePower_norm_right :
    (∏ p : P, (Ideal.absNorm p.val.asIdeal : ℝ) ^
      idealPrimeMultiplicity K p.val J) = (Ideal.absNorm J : ℝ) := by
  have g : ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)),
      (∏ p : s, (Ideal.absNorm p.val.asIdeal : ℝ) ^ idealPrimeMultiplicity K p.val I) =
        ∏ p ∈ s, (Ideal.absNorm p.asIdeal : ℝ) ^ idealPrimeMultiplicity K p I :=
    fun s I => Finset.prod_coe_sort s
      (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ idealPrimeMultiplicity K p I)
  rw [g]
  have h := prod_joint_primePower_norm K J C hJ hC
  rw [g] at h
  simpa only [jointPlaces, Finset.union_comm] using h

/-- Every joint prime appears positively in at least one actual ideal. -/
theorem joint_multiplicity_sum_pos (p : P) :
    0 < idealPrimeMultiplicity K p.val C + idealPrimeMultiplicity K p.val J := by
  rcases Finset.mem_union.mp p.property with hp | hp
  · have he : idealPrimeMultiplicity K p.val C ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hC p.val.irreducible).mpr
        ((mem_sexticIdealPlaces_iff K C hC p.val).mp hp)
    exact (Nat.pos_of_ne_zero he).trans_le (Nat.le_add_right _ _)
  · have he : idealPrimeMultiplicity K p.val J ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hJ p.val.irreducible).mpr
        ((mem_sexticIdealPlaces_iff K J hJ p.val).mp hp)
    exact (Nat.pos_of_ne_zero he).trans_le (Nat.le_add_left _ _)

/-- Literal joint radical, including overlapping prime supports only once. -/
theorem jointRadical_absNorm_le_real :
    (Ideal.absNorm (jointRadical K C J hC hJ) : ℝ) ≤
      (Ideal.absNorm C : ℝ) * (Ideal.absNorm J : ℝ) := by
  calc
    _ = ∏ p : P, (Ideal.absNorm p.val.asIdeal : ℝ) := by
      simp only [jointRadical, map_prod, Nat.cast_prod]
    _ ≤ ∏ p : P, (Ideal.absNorm p.val.asIdeal : ℝ) ^ idealPrimeMultiplicity K p.val C *
          (Ideal.absNorm p.val.asIdeal : ℝ) ^ idealPrimeMultiplicity K p.val J := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro p _
      have hq : (1 : ℝ) ≤ (Ideal.absNorm p.val.asIdeal : ℝ) := by
        have hp : 0 < Ideal.absNorm p.val.asIdeal :=
          Ideal.absNorm_pos_of_nonZeroDivisors
            (⟨p.val.asIdeal, mem_nonZeroDivisors_of_ne_zero p.val.ne_bot⟩ : (Ideal (𝓞 K))⁰)
        exact_mod_cast Nat.succ_le_iff.mpr hp
      rw [← pow_add]
      exact le_self_pow₀ hq (joint_multiplicity_sum_pos K C J hC hJ p).ne'
    _ = _ := by
      rw [Finset.prod_mul_distrib, prod_joint_primePower_norm K C J hC hJ,
        prod_joint_primePower_norm_right K C J hC hJ]

theorem jointRadical_absNorm_le :
    Ideal.absNorm (jointRadical K C J hC hJ) ≤ Ideal.absNorm C * Ideal.absNorm J := by
  exact_mod_cast jointRadical_absNorm_le_real K C J hC hJ

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- For any supplied fixed depth, the entire S factor is explicit. -/
theorem fixedChartPeriodIdeal_absNorm_le (N : ℕ) (c k : NZ) :
    (Ideal.absNorm (fixedChartPeriodIdeal K S ζ hζ c k N).val : ℝ) ≤
      (Ideal.absNorm (clearedSModulus K S ζ hζ N) : ℝ) *
        (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ) := by
  change (Ideal.absNorm (clearedSModulus K S ζ hζ N *
    jointRadical K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
      (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)) : ℝ) ≤ _
  rw [map_mul, Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_left
    (jointRadical_absNorm_le_real K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
      (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k))
    (Nat.cast_nonneg _)).trans_eq (mul_assoc _ _ _).symm

/-- C0 is chosen BEFORE both actual nonzero S-integers c and k.
When the denominator-clearing depth is fixed (for example 2H), the S factor
is consequently a genuine fixed constant in the period comparison. -/
theorem exists_fixedChartPeriodIdeal_norm_constant (N : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ c k : NZ,
      (Ideal.absNorm (fixedChartPeriodIdeal K S ζ hζ c k N).val : ℝ) ≤
        C0 * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ) := by
  refine ⟨(Ideal.absNorm (clearedSModulus K S ζ hζ N) : ℝ), ?_, ?_⟩
  · let I : (Ideal (𝓞 K))⁰ := ⟨clearedSModulus K S ζ hζ N,
      mem_nonZeroDivisors_of_ne_zero (clearedSModulus_ne_zero K S ζ hζ N)⟩
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  · exact fixedChartPeriodIdeal_absNorm_le K S ζ hζ N

end HeckeGeneral.Characters.ActualGramPeriodNormDraft
