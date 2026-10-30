import HeckeGeneral.Analysis.ActualSIntegerAmplifierMask
import HeckeGeneral.Analysis.SIntegerSexticMellinAmplification

/-! Exact divisor amplification with an arbitrary actual base row.
The additional coefficient is the literal inverse sextic evaluation of
the divisor at that base row. Its zeros are retained. No moving row is
extended to a Hecke character. -/

noncomputable section
namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.ActualSIntegerMoments
open AlgebraicNumberTheory.PowerResidueSymbols UniqueFactorizationMonoid
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

theorem idealPrimeMultiplicity_squarefreeIdeal
    (T : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) :
    idealPrimeMultiplicity K p (squarefreeIdeal K T).val = if p ∈ T then 1 else 0 := by
  unfold idealPrimeMultiplicity
  rw [Ideal.count_associates_factors_eq
    (nonZeroDivisors.coe_ne_zero (squarefreeIdeal K T)) p.isPrime p.ne_bot]
  rw [← primeExponents_apply, primeExponents_squarefreeIdeal]

/-- A concrete local symbol on the envelope; outside the envelope the
value is irrelevant to the products below. -/
def sexticPrimeEnvelopeEvaluation (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (p : HeightOneSpectrum (𝓞 K)) (u : S.integer K) : ℂ :=
  if hp : p ∈ E then sIntegerSexticEvaluation K S p (hES p hp) ζ hζ σ (hE6 p hp) u
  else 0

theorem sexticEnvelopeEvaluation_eq_primeProduct
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ E) (u : S.integer K) :
    sexticEnvelopeEvaluation K S ζ hζ σ E hES hE6 T hT u =
      ∏ p ∈ T, sexticPrimeEnvelopeEvaluation K S ζ hζ σ E hES hE6 p u := by
  letI : Fintype (idealPrimeDivisors K (squarefreeIdeal K T).val) :=
    (idealPrimeDivisors_finite K _ (nonZeroDivisors.coe_ne_zero (squarefreeIdeal K T))).fintype
  unfold sexticEnvelopeEvaluation sIntegerSexticIdealEvaluation
  apply Finset.prod_bij (fun p _ => p.val)
  · intro p _
    exact (prime_dvd_primeProduct_iff K p.val T).mp p.property
  · intro p _ q _ hpq
    exact Subtype.ext hpq
  · intro p hp
    exact ⟨⟨p, (prime_dvd_primeProduct_iff K p T).mpr hp⟩, Finset.mem_univ _, rfl⟩
  · intro p _
    have hpT := (prime_dvd_primeProduct_iff K p.val T).mp p.property
    rw [idealPrimeMultiplicity_squarefreeIdeal, ite_eq_left hpT, pow_one]
    simp only [sexticPrimeEnvelopeEvaluation, dite_eq_left (hT hpT)]

/-- Denominator multiplicativity is proved from the actual prime product,
including all nonunit numerator zeros. -/
theorem zeroExtendedSexticIdealEvaluation_squarefree_union
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (A B : Finset (HeightOneSpectrum (𝓞 K))) (hA : A ⊆ E) (hB : B ⊆ E)
    (hd : Disjoint A B) (u : S.integer K) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ (squarefreeIdeal K (A ∪ B)) u =
      zeroExtendedSexticIdealEvaluation K S ζ hζ σ (squarefreeIdeal K A) u *
        zeroExtendedSexticIdealEvaluation K S ζ hζ σ (squarefreeIdeal K B) u := by
  rw [zeroExtendedSexticIdealEvaluation_squarefreeIdeal K S ζ hζ σ E hES hE6
    (A ∪ B) (Finset.union_subset hA hB),
    zeroExtendedSexticIdealEvaluation_squarefreeIdeal K S ζ hζ σ E hES hE6 A hA,
    zeroExtendedSexticIdealEvaluation_squarefreeIdeal K S ζ hζ σ E hES hE6 B hB]
  simp only [sexticEnvelopeEvaluation_eq_primeProduct]
  exact Finset.prod_union hd

theorem actualInverseIdealCoefficient_squarefree_union
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (η : HeckeCharacter K) (u : S.integer K)
    (A B : Finset (HeightOneSpectrum (𝓞 K))) (hA : A ⊆ E) (hB : B ⊆ E)
    (hd : Disjoint A B) :
    actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K (A ∪ B)) =
      actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K A) *
        actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K B) := by
  unfold actualInverseIdealCoefficient
  rw [moebius_squarefree_union K A B hd,
    zeroExtendedSexticIdealEvaluation_squarefree_union K S ζ hζ σ E hES hE6 A B hA hB hd,
    squarefreeIdeal_union K A B hd, heckeIdealCoefficient_mul, mul_zpow]
  ring

theorem sexticRowPolynomial_eq_sum_coeff
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (η : HeckeCharacter K) (u : S.integer K) (D : ℝ) (W : ℝ → ℂ) :
    sexticRowPolynomial K S ζ hζ σ E hES hE6 η u D W =
      (Real.sqrt D : ℂ)⁻¹ * ∑ T ∈ E.powerset,
        actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K T) *
          W (idealNorm K (squarefreeIdeal K T) / D) := by
  unfold sexticRowPolynomial
  congr 1
  rw [← Finset.sum_attach E.powerset]
  apply Finset.sum_congr rfl
  intro T _
  rw [actualInverseIdealCoefficient,
    zeroExtendedSexticIdealEvaluation_squarefreeIdeal K S ζ hζ σ E hES hE6
      T.val (Finset.mem_powerset.mp T.property)]

theorem actualInverseIdealCoefficient_sixth_mul
    (η : HeckeCharacter K) (u a : S.integer K) (I : NonzeroIdeal K) :
    actualInverseIdealCoefficient K S ζ hζ σ η (a ^ 6 * u) I =
      if IsCoprime I.val (sIntegerModulusContraction K S a) then
        actualInverseIdealCoefficient K S ζ hζ σ η u I else 0 := by
  by_cases hI : sexticIdealOutsideS K S I
  · unfold actualInverseIdealCoefficient
    simp only [zeroExtendedSexticIdealEvaluation, dite_eq_left hI]
    rw [sIntegerSexticIdealEvaluation_mul,
      sIntegerSexticIdealEvaluation_sixth_power_coprime_mask]
    by_cases hc : IsCoprime I.val (sIntegerModulusContraction K S a) <;> simp [hc]
  · simp [actualInverseIdealCoefficient,
      zeroExtendedSexticIdealEvaluation_eq_zero K S ζ hζ σ I _ hI]

theorem sexticRowPolynomial_sixth_mul
    (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ P ∪ Q, p ∉ S) (hE6 : ∀ p ∈ P ∪ Q, (6 : 𝓞 K) ∉ p.asIdeal)
    (η : HeckeCharacter K) (u a : S.integer K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a)
    (D : ℝ) (W : ℝ → ℂ) :
    sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η (a ^ 6 * u) D W =
      (Real.sqrt D : ℂ)⁻¹ * ∑ T ∈ Q.powerset,
        actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K T) *
          W (idealNorm K (squarefreeIdeal K T) / D) := by
  rw [sexticRowPolynomial_eq_sum_coeff]
  congr 1
  have he : (P ∪ Q).powerset.filter (fun T => T ⊆ Q) = Q.powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans Finset.subset_union_right, h⟩⟩
  rw [← he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  rw [actualInverseIdealCoefficient_sixth_mul,
    squarefreeIdeal_coprime_contraction_iff_subset K S P Q a hP hQ T
      (Finset.mem_powerset.mp hT)]
  by_cases ht : T ⊆ Q <;> simp [ht]

/-- Exact normalized arbitrary-base amplification; the divisor coefficient
contains the actual base evaluation, rather than an unmasked Hecke coefficient. -/
theorem sexticRowPolynomial_base_amplification
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (hd : Disjoint P Q)
    (hES : ∀ p ∈ P ∪ Q, p ∉ S) (hE6 : ∀ p ∈ P ∪ Q, (6 : 𝓞 K) ∉ p.asIdeal)
    (η : HeckeCharacter K) (u a : S.integer K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a)
    {D : ℝ} (hD : 0 < D) (W : ℝ → ℂ) :
    sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η u D W =
      ∑ A ∈ P.powerset,
        actualInverseIdealCoefficient K S ζ hζ σ η u (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          sexticRowPolynomial K S ζ hζ σ (P ∪ Q) hES hE6 η (a ^ 6 * u)
            (D / idealNorm K (squarefreeIdeal K A)) W := by
  rw [sexticRowPolynomial_eq_sum_coeff, sum_powerset_disjoint_union P Q hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sexticRowPolynomial_sixth_mul K S ζ hζ σ P Q hES hE6 η u a hP hQ]
  rw [sqrt_scale_amplification hD (idealNorm_pos K (squarefreeIdeal K A))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hdAB : Disjoint A B := hd.mono (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
  rw [actualInverseIdealCoefficient_squarefree_union K S ζ hζ σ (P ∪ Q) hES hE6 η u
    A B ((Finset.mem_powerset.mp hA).trans Finset.subset_union_left)
      ((Finset.mem_powerset.mp hB).trans Finset.subset_union_right) hdAB,
    idealNorm_squarefree_union K A B hdAB, div_div_eq_mul_div]
  ring

end HeckeGeneral.Analysis.SquarefreeAmplification
