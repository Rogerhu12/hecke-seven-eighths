import HeckeGeneral.Analysis.ActualSIntegerZeroSlotMI
import HeckeGeneral.Analysis.SIntegerSexticAmplificationEnergy

/-!
Exact amplification for the actual complex Mellin family W_s(y)=W(y)y^(-s).
All support statements are proved from the fixed smooth dyadic cutoff.
This extends the finite identity needed by compact-in-s analytic continuation;
it does not assume a uniform growth or a moment estimate for that family.
-/

noncomputable section
namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.ActualSIntegerMoments UniqueFactorizationMonoid
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

def dyadicSexticMellinInversePolynomial (η : HeckeCharacter K)
    (u : S.integer K) (D : ℝ) (s : ℂ) : ℂ :=
  sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (dyadicIdealSupport K D)
    u D (dyadicMellinWeight s)

theorem dyadicSexticMellinInversePolynomial_eq_orbit
    (η : HeckeCharacter K) (u : NonzeroRingElements (S.integer K)) (D : ℝ) (s : ℂ) :
    dyadicSexticMellinInversePolynomial K S ζ hζ σ η u.val D s =
      actualSIntegerInversePolynomial K S ζ hζ σ η (Quotient.mk _ u) D s := rfl

theorem sIntegerSexticInverseIdealTerm_mellin (η : HeckeCharacter K)
    (u : S.integer K) (D : ℝ) (s : ℂ) (I : NonzeroIdeal K) :
    sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D (dyadicMellinWeight s) I =
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D sexticDyadicWeight I *
        (idealNorm K I / D : ℂ) ^ (-s) := by
  simp only [sIntegerSexticInverseIdealTerm, dyadicMellinWeight, Complex.ofReal_div]
  ring

theorem dyadicSexticMellinTerm_eq_zero_of_notMem (η : HeckeCharacter K)
    (u : S.integer K) {D : ℝ} (hD : 0 < D) (s : ℂ) (I : NonzeroIdeal K)
    (hI : I ∉ dyadicIdealSupport K D) :
    sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D (dyadicMellinWeight s) I = 0 := by
  rw [sIntegerSexticInverseIdealTerm_mellin,
    dyadicSexticTerm_eq_zero_of_notMem K S ζ hζ σ η u hD I hI, zero_mul]

theorem dyadicSexticMellinTerm_primeSupport_subset (η : HeckeCharacter K)
    (u : S.integer K) {r D : ℝ} (hr : 0 < r) (hrD : r ≤ D) (s : ℂ)
    (I : NonzeroIdeal K)
    (hI : sIntegerSexticInverseIdealTerm K S ζ hζ σ η u r (dyadicMellinWeight s) I ≠ 0) :
    idealPrimeSupport K I ⊆ dyadicSexticPrimeEnvelope K S D := by
  rw [sIntegerSexticInverseIdealTerm_mellin] at hI
  exact dyadicSexticTerm_primeSupport_subset K S ζ hζ σ η u hr hrD I
    (mul_ne_zero_iff.mp hI).1

/-- Same actual amplifier and same test at every divisor scale, now for all
complex s. There are no remaining finite-support or covering hypotheses. -/
theorem dyadicSexticMellinInversePolynomial_amplification
    (η : HeckeCharacter K) (a : S.integer K) {D : ℝ} (hD : 0 < D) (s : ℂ) :
    dyadicSexticMellinInversePolynomial K S ζ hζ σ η 1 D s =
      ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
        sexticAmplifierCoefficient K η A *
          dyadicSexticMellinInversePolynomial K S ζ hζ σ η (a ^ 6)
            (D / idealNorm K (squarefreeIdeal K A)) s := by
  have hES : ∀ p ∈ dyadicDividingPrimes K S a D ∪ dyadicNondividingPrimes K S a D,
      p ∉ S := by
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticPrimeEnvelope_outsideS K S D
  have hE6 : ∀ p ∈ dyadicDividingPrimes K S a D ∪ dyadicNondividingPrimes K S a D,
      (6 : 𝓞 K) ∉ p.asIdeal := by
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticPrimeEnvelope_awaySix K S D
  have hP : ∀ p ∈ dyadicDividingPrimes K S a D,
      p.asIdeal ∣ sIntegerModulusContraction K S a := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hQ : ∀ p ∈ dyadicNondividingPrimes K S a D,
      ¬p.asIdeal ∣ sIntegerModulusContraction K S a := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  apply sIntegerSexticInverseIdealPolynomial_amplification K S ζ hζ σ η
    (dyadicIdealSupport K) (dyadicDividingPrimes K S a D)
    (dyadicNondividingPrimes K S a D) (dyadicPrimes_disjoint K S a D)
    hES hE6 a hP hQ hD (dyadicMellinWeight s)
  · intro I _ ht
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticMellinTerm_primeSupport_subset K S ζ hζ σ η 1 hD le_rfl s I ht
  · exact dyadicSexticMellinTerm_eq_zero_of_notMem K S ζ hζ σ η 1 hD s
  · intro A _ I _ ht
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticMellinTerm_primeSupport_subset K S ζ hζ σ η (a ^ 6)
      (div_pos hD (idealNorm_pos K (squarefreeIdeal K A)))
      (div_le_self hD.le (one_le_idealNorm K (squarefreeIdeal K A))) s I ht
  · intro A _
    exact dyadicSexticMellinTerm_eq_zero_of_notMem K S ζ hζ σ η (a ^ 6)
      (div_pos hD (idealNorm_pos K (squarefreeIdeal K A))) s

theorem dyadicSexticMellinInversePolynomial_sq_le
    (η : HeckeCharacter K) (a : S.integer K) {D W B : ℝ} (hD : 0 < D)
    (s : ℂ) (hB : 0 ≤ B)
    (hmass : ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖sexticAmplifierCoefficient K η A‖ ≤ W)
    (hrow : ∀ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖dyadicSexticMellinInversePolynomial K S ζ hζ σ η (a ^ 6)
        (D / idealNorm K (squarefreeIdeal K A)) s‖ ^ 2 ≤ B) :
    ‖dyadicSexticMellinInversePolynomial K S ζ hζ σ η 1 D s‖ ^ 2 ≤ W ^ 2 * B := by
  rw [dyadicSexticMellinInversePolynomial_amplification K S ζ hζ σ η a hD s]
  exact norm_sum_mul_sq_le_mass_sq _ (sexticAmplifierCoefficient K η)
    (fun A => dyadicSexticMellinInversePolynomial K S ζ hζ σ η (a ^ 6)
      (D / idealNorm K (squarefreeIdeal K A)) s) hB hmass hrow

end HeckeGeneral.Analysis.SquarefreeAmplification
