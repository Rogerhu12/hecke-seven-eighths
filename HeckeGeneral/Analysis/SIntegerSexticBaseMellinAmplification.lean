import HeckeGeneral.Analysis.SIntegerSexticBaseAmplification

/-! Concrete dyadic Mellin amplification for every actual base numerator.
Support is obtained from the fixed dyadic test, with a common envelope at
all divisor scales. Coefficient norms are bounded by the already proved
Hecke/Moebius amplifier mass; no Hecke extension of a row is used. -/

noncomputable section
namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- The actual divisor coefficient at the base numerator. -/
def sexticBaseAmplifierCoefficient (η : HeckeCharacter K) (u : S.integer K)
    (A : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K A) *
    (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹

theorem sexticBaseAmplifierCoefficient_eq (η : HeckeCharacter K) (u : S.integer K)
    (A : Finset (HeightOneSpectrum (𝓞 K))) :
    sexticBaseAmplifierCoefficient K S ζ hζ σ η u A =
      sexticAmplifierCoefficient K η A *
        zeroExtendedSexticIdealEvaluation K S ζ hζ σ (squarefreeIdeal K A) u ^ (-1 : ℤ) := by
  unfold sexticBaseAmplifierCoefficient actualInverseIdealCoefficient sexticAmplifierCoefficient
  ring

theorem norm_zeroExtendedSexticIdealEvaluation_inverse_le_one
    (I : NonzeroIdeal K) (u : S.integer K) :
    ‖zeroExtendedSexticIdealEvaluation K S ζ hζ σ I u ^ (-1 : ℤ)‖ ≤ 1 := by
  by_cases hI : sexticIdealOutsideS K S I
  · rw [zeroExtendedSexticIdealEvaluation, dite_eq_left hI]
    by_cases hz : sIntegerSexticIdealEvaluation K S ζ hζ σ I.val
        (nonZeroDivisors.coe_ne_zero I) (fun p hp => (hI p hp).1)
          (fun p hp => (hI p hp).2) u = 0
    · simp [hz]
    · have hn := norm_sIntegerSexticIdealEvaluation_eq_one K S ζ hζ σ I.val
        (nonZeroDivisors.coe_ne_zero I) (fun p hp => (hI p hp).1)
        (fun p hp => (hI p hp).2) u (by
          intro p hp hzero
          exact hz (sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S ζ hζ σ I.val
            (nonZeroDivisors.coe_ne_zero I) (fun p hp => (hI p hp).1)
              (fun p hp => (hI p hp).2) u p hp hzero))
      simp only [zpow_neg_one, norm_inv, hn, inv_one, le_refl]
  · simp [zeroExtendedSexticIdealEvaluation_eq_zero K S ζ hζ σ I u hI]

theorem norm_sexticBaseAmplifierCoefficient_le
    (η : HeckeCharacter K) (u : S.integer K) (A : Finset (HeightOneSpectrum (𝓞 K))) :
    ‖sexticBaseAmplifierCoefficient K S ζ hζ σ η u A‖ ≤ ‖sexticAmplifierCoefficient K η A‖ := by
  rw [sexticBaseAmplifierCoefficient_eq, norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (norm_zeroExtendedSexticIdealEvaluation_inverse_le_one K S ζ hζ σ _ u)
      (norm_nonneg _)).trans_eq (mul_one _)

/-- Every scale uses the actual polynomial and the same Mellin profile.
There are no support assumptions, and base-row zeros remain in the exact
divisor coefficient and in every amplified row. -/
theorem dyadicSexticMellinInversePolynomial_base_amplification
    (η : HeckeCharacter K) (u a : S.integer K) {D : ℝ} (hD : 0 < D) (s : ℂ) :
    dyadicSexticMellinInversePolynomial K S ζ hζ σ η u D s =
      ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
        sexticBaseAmplifierCoefficient K S ζ hζ σ η u A *
          dyadicSexticMellinInversePolynomial K S ζ hζ σ η (a ^ 6 * u)
            (D / idealNorm K (squarefreeIdeal K A)) s := by
  let P := dyadicDividingPrimes K S a D
  let Q := dyadicNondividingPrimes K S a D
  have hES : ∀ p ∈ P ∪ Q, p ∉ S := by
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticPrimeEnvelope_outsideS K S D
  have hE6 : ∀ p ∈ P ∪ Q, (6 : 𝓞 K) ∉ p.asIdeal := by
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticPrimeEnvelope_awaySix K S D
  have hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have heq (v : S.integer K) (r : ℝ) (hr : 0 < r) (hrD : r ≤ D) :
      dyadicSexticMellinInversePolynomial K S ζ hζ σ η v r s =
        sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η v r (dyadicMellinWeight s) := by
    apply sIntegerSexticInverseIdealPolynomial_eq_rowPolynomial
    · intro I _ ht
      rw [dyadicPrimes_union K S a D]
      exact dyadicSexticMellinTerm_primeSupport_subset K S ζ hζ σ η v hr hrD s I ht
    · intro I _ hIF
      exact dyadicSexticMellinTerm_eq_zero_of_notMem K S ζ hζ σ η v hr s I hIF
  rw [heq u D hD le_rfl, sexticRowPolynomial_base_amplification K S ζ hζ σ P Q
    (dyadicPrimes_disjoint K S a D) hES hE6 η u a hP hQ hD]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [heq (a ^ 6 * u) (D / idealNorm K (squarefreeIdeal K A))
    (div_pos hD (idealNorm_pos K _)) (div_le_self hD.le (one_le_idealNorm K _))]
  rfl

/-- Weighted Cauchy consumes the exact arbitrary-base identity. -/
theorem dyadicSexticMellinInversePolynomial_base_sq_le
    (η : HeckeCharacter K) (u a : S.integer K) {D W B : ℝ} (hD : 0 < D)
    (s : ℂ) (hB : 0 ≤ B)
    (hmass : ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖sexticAmplifierCoefficient K η A‖ ≤ W)
    (hrow : ∀ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖dyadicSexticMellinInversePolynomial K S ζ hζ σ η (a ^ 6 * u)
        (D / idealNorm K (squarefreeIdeal K A)) s‖ ^ 2 ≤ B) :
    ‖dyadicSexticMellinInversePolynomial K S ζ hζ σ η u D s‖ ^ 2 ≤ W ^ 2 * B := by
  rw [dyadicSexticMellinInversePolynomial_base_amplification K S ζ hζ σ η u a hD s]
  apply norm_sum_mul_sq_le_mass_sq _ (sexticBaseAmplifierCoefficient K S ζ hζ σ η u)
    (fun A => dyadicSexticMellinInversePolynomial K S ζ hζ σ η (a ^ 6 * u)
      (D / idealNorm K (squarefreeIdeal K A)) s) hB _ hrow
  exact (Finset.sum_le_sum fun A _ =>
    norm_sexticBaseAmplifierCoefficient_le K S ζ hζ σ η u A).trans hmass

end HeckeGeneral.Analysis.SquarefreeAmplification
