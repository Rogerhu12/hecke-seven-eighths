import HeckeGeneral.Analysis.SIntegerSexticAmplificationEnergy
import HeckeGeneral.Analysis.IdealMobiusReciprocal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
The divisor coefficient mass in sixth-power amplification is a small power
of the actual amplifier ideal norm.  Constants depend only on K and the
positive loss, and are uniform in the Hecke character, prime subset and
ideal.  This is an arithmetic estimate, with no MI or row-count assumption.
-/

noncomputable section
namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.IdealMobiusMask Filter
open scoped BigOperators Classical nonZeroDivisors Topology

variable (K : Type*) [Field K] [NumberField K]

theorem norm_sexticAmplifierCoefficient_le_one (η : HeckeCharacter K)
    (A : Finset (HeightOneSpectrum (𝓞 K))) :
    ‖sexticAmplifierCoefficient K η A‖ ≤ 1 := by
  have hm : ‖(UniqueFactorizationMonoid.moebius (squarefreeIdeal K A).val : ℂ) *
      heckeIdealCoefficient K η (squarefreeIdeal K A)‖ ≤ 1 := by
    have hμ : ‖(UniqueFactorizationMonoid.moebius (squarefreeIdeal K A).val : ℂ)‖ = 1 := by
      simp [squarefreeIdeal, moebius_primeProduct, Int.cast_pow]
    rw [norm_mul, hμ, one_mul]
    exact norm_heckeIdealCoefficient_le_one K η (squarefreeIdeal K A)
  have hsqrt : 1 ≤ Real.sqrt (idealNorm K (squarefreeIdeal K A)) :=
    Real.one_le_sqrt.mpr (one_le_idealNorm K _)
  have hinv : ‖(Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ hsqrt
  rw [sexticAmplifierCoefficient, norm_mul]
  exact (mul_le_mul hm hinv (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem sexticAmplifierCoefficient_mass_le_two_pow (η : HeckeCharacter K)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑ A ∈ T.powerset, ‖sexticAmplifierCoefficient K η A‖) ≤ (2 : ℝ) ^ T.card := by
  calc
    _ ≤ ∑ _A ∈ T.powerset, (1 : ℝ) := Finset.sum_le_sum fun A _ =>
      norm_sexticAmplifierCoefficient_le_one K η A
    _ = _ := by simp

theorem idealNorm_squarefreeIdeal_eq_prod (T : Finset (HeightOneSpectrum (𝓞 K))) :
    idealNorm K (squarefreeIdeal K T) = ∏ p ∈ T, (Ideal.absNorm p.asIdeal : ℝ) := by
  simp [idealNorm, squarefreeIdeal, primeProduct, map_prod, Nat.cast_prod]

/-- A finite set of small prime ideals absorbs the constant; each remaining
prime contributes 2 at a cost at most its norm to the positive power δ. -/
theorem exists_two_pow_card_le_idealNorm_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : Finset (HeightOneSpectrum (𝓞 K)),
      (2 : ℝ) ^ T.card ≤ C * idealNorm K (squarefreeIdeal K T) ^ δ := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (2 : ℝ)))
  obtain ⟨N, hN⟩ := exists_nat_ge R
  let E : Finset (HeightOneSpectrum (𝓞 K)) :=
    (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 K) N).toFinset
  have hlarge (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ E) :
      2 ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ δ := by
    have hpN : N < Ideal.absNorm p.asIdeal := by
      simpa [E] using hp
    exact hR _ (hN.trans (by exact_mod_cast hpN.le))
  refine ⟨(2 : ℝ) ^ E.card, by positivity, fun T => ?_⟩
  let b : HeightOneSpectrum (𝓞 K) → ℝ := fun p => if p ∈ E then 2 else 1
  have hb (p : HeightOneSpectrum (𝓞 K)) :
      2 ≤ b p * (Ideal.absNorm p.asIdeal : ℝ) ^ δ := by
    by_cases hp : p ∈ E
    · have hq : 1 ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ δ :=
        Real.one_le_rpow (one_le_idealNorm K (primeNonzeroIdeal K p)) hδ.le
      simp only [b, ite_eq_left hp]
      linarith
    · simpa [b, hp] using hlarge p hp
  have hprodB : (∏ p ∈ T, b p) ≤ (2 : ℝ) ^ E.card := by
    have heq : (∏ p ∈ T, b p) = (2 : ℝ) ^ (T ∩ E).card := by
      simp [b]
    rw [heq]
    exact pow_le_pow_right₀ (by norm_num)
      (Finset.card_le_card Finset.inter_subset_right)
  calc
    _ = ∏ _p ∈ T, (2 : ℝ) := by simp
    _ ≤ ∏ p ∈ T, b p * (Ideal.absNorm p.asIdeal : ℝ) ^ δ :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun p _ => hb p)
    _ = (∏ p ∈ T, b p) * idealNorm K (squarefreeIdeal K T) ^ δ := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow T
        (fun p => (Ideal.absNorm p.asIdeal : ℝ)) (fun _ _ => Nat.cast_nonneg _) δ,
        idealNorm_squarefreeIdeal_eq_prod]
    _ ≤ (2 : ℝ) ^ E.card * idealNorm K (squarefreeIdeal K T) ^ δ :=
      mul_le_mul_of_nonneg_right hprodB (Real.rpow_nonneg (idealNorm_pos K _).le _)

theorem squarefreeIdeal_dvd_of_primeSupport_subset
    (I : NonzeroIdeal K) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T ⊆ idealPrimeSupport K I) : (squarefreeIdeal K T).val ∣ I.val := by
  exact Finset.prod_dvd_of_coprime (pairwise_coprime_primeIdeals T)
    (fun p hp => (mem_idealPrimeSupport_iff K I p).mp (hT hp))

theorem idealNorm_squarefreeIdeal_le_of_primeSupport_subset
    (I : NonzeroIdeal K) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T ⊆ idealPrimeSupport K I) :
    idealNorm K (squarefreeIdeal K T) ≤ idealNorm K I := by
  change (Ideal.absNorm (squarefreeIdeal K T).val : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I)
    (map_dvd Ideal.absNorm (squarefreeIdeal_dvd_of_primeSupport_subset K I T hT))

/-- Uniform small-power divisor mass, even for an arbitrary subset of the
actual prime divisors. This includes the scale-truncated dyadic envelope. -/
theorem sexticAmplifierCoefficient_mass_small_power {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeCharacter K) (I : NonzeroIdeal K)
      (T : Finset (HeightOneSpectrum (𝓞 K))), T ⊆ idealPrimeSupport K I →
      (∑ A ∈ T.powerset, ‖sexticAmplifierCoefficient K η A‖) ≤
        C * idealNorm K I ^ δ := by
  obtain ⟨C, hC, hbound⟩ := exists_two_pow_card_le_idealNorm_rpow K hδ
  refine ⟨C, hC, fun η I T hT => ?_⟩
  exact (sexticAmplifierCoefficient_mass_le_two_pow K η T).trans
    ((hbound T).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (idealNorm_pos K _).le
        (idealNorm_squarefreeIdeal_le_of_primeSupport_subset K I T hT) hδ.le) hC.le))

end HeckeGeneral.Analysis.SquarefreeAmplification
