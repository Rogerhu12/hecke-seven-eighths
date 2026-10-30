import HeckeGeneral.Analysis.SIntegerSexticFiniteIdealSum
import HeckeGeneral.Analysis.SmoothDyadicPartition

/-!
Concrete smooth dyadic amplification with actual norm-bounded ideal supports.
The weight is the frozen smooth partition weight.  The finite set at scale r
contains every nonzero integral ideal of norm at most 2r; no support hypothesis
is supplied.  At all scales D/q_A one common prime envelope is constructed
from the norm bound 2D and filtered only by the fixed S and the primes of 6.
This is an exact finite-sum identity, not a counting or MI energy estimate.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.IdealMobiusMask HeckeGeneral.Characters
open UniqueFactorizationMonoid
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- The concrete smooth real partition weight, regarded as a complex test. -/
def sexticDyadicWeight (y : ℝ) : ℂ := (fixedDyadicWeight y : ℂ)

/-- Actual nonzero integral ideals with norm at most the natural floor of 2D. -/
def dyadicIdealSupport (D : ℝ) : Finset (NonzeroIdeal K) :=
  (Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 K) ⌊2 * D⌋₊).toFinset

theorem mem_dyadicIdealSupport_iff {D : ℝ} (hD : 0 ≤ D) (I : NonzeroIdeal K) :
    I ∈ dyadicIdealSupport K D ↔ idealNorm K I ≤ 2 * D := by
  simp only [dyadicIdealSupport, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact Nat.le_floor_iff (by positivity)

/-- Delete only the fixed exceptional primes from the actual bounded envelope. -/
def dyadicSexticPrimeEnvelope (D : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finitePrimeEnvelope K (dyadicIdealSupport K D)).filter
    (fun p => p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal)

omit [Finite S] in
theorem dyadicSexticPrimeEnvelope_outsideS (D : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ dyadicSexticPrimeEnvelope K S D) :
    p ∉ S := (Finset.mem_filter.mp hp).2.1

omit [Finite S] in
theorem dyadicSexticPrimeEnvelope_awaySix (D : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ dyadicSexticPrimeEnvelope K S D) :
    (6 : 𝓞 K) ∉ p.asIdeal := (Finset.mem_filter.mp hp).2.2

/-- The compact support of the actual test bounds every nonzero actual term. -/
theorem idealNorm_lt_of_dyadicSexticTerm_ne_zero
    (η : HeckeCharacter K) (u : S.integer K) {r : ℝ} (hr : 0 < r)
    (I : NonzeroIdeal K)
    (ht : sIntegerSexticInverseIdealTerm K S ζ hζ σ η u r sexticDyadicWeight I ≠ 0) :
    idealNorm K I < 2 * r := by
  have hw : fixedDyadicWeight (idealNorm K I / r) ≠ 0 := by
    intro hw
    apply ht
    simp [sIntegerSexticInverseIdealTerm, sexticDyadicWeight, hw]
  have hy : idealNorm K I / r < 2 := by
    by_contra h
    exact hw (fixedDyadicWeight_zero_of_ge (le_of_not_gt h))
  exact (div_lt_iff₀ hr).mp hy

theorem dyadicSexticTerm_eq_zero_of_notMem
    (η : HeckeCharacter K) (u : S.integer K) {r : ℝ} (hr : 0 < r)
    (I : NonzeroIdeal K) (hI : I ∉ dyadicIdealSupport K r) :
    sIntegerSexticInverseIdealTerm K S ζ hζ σ η u r sexticDyadicWeight I = 0 := by
  by_contra ht
  apply hI
  exact (mem_dyadicIdealSupport_iff K hr.le I).mpr
    (idealNorm_lt_of_dyadicSexticTerm_ne_zero K S ζ hζ σ η u hr I ht).le

/-- One envelope at D covers every nonzero actual term at every 0 < r ≤ D. -/
theorem dyadicSexticTerm_primeSupport_subset
    (η : HeckeCharacter K) (u : S.integer K) {r D : ℝ}
    (hr : 0 < r) (hrD : r ≤ D) (I : NonzeroIdeal K)
    (ht : sIntegerSexticInverseIdealTerm K S ζ hζ σ η u r sexticDyadicWeight I ≠ 0) :
    idealPrimeSupport K I ⊆ dyadicSexticPrimeEnvelope K S D := by
  have hI : I ∈ dyadicIdealSupport K D := by
    apply (mem_dyadicIdealSupport_iff K (hr.le.trans hrD) I).mpr
    exact (idealNorm_lt_of_dyadicSexticTerm_ne_zero K S ζ hζ σ η u hr I ht).le.trans
      (mul_le_mul_of_nonneg_left hrD (by norm_num))
  have hgood : sexticIdealOutsideS K S I := by
    by_contra h
    exact ht (sIntegerSexticInverseIdealTerm_eq_zero_of_deleted K S ζ hζ σ η u
      r sexticDyadicWeight I h)
  intro p hp
  exact Finset.mem_filter.mpr
    ⟨idealPrimeSupport_subset_envelope K (dyadicIdealSupport K D) I hI hp,
      hgood p ((mem_idealPrimeSupport_iff K I p).mp hp)⟩

/-- The dividing and nondividing parts of the same concrete prime envelope. -/
def dyadicDividingPrimes (a : S.integer K) (D : ℝ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (dyadicSexticPrimeEnvelope K S D).filter
    (fun p => p.asIdeal ∣ sIntegerModulusContraction K S a)

def dyadicNondividingPrimes (a : S.integer K) (D : ℝ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (dyadicSexticPrimeEnvelope K S D).filter
    (fun p => ¬p.asIdeal ∣ sIntegerModulusContraction K S a)

omit [Finite S] in
theorem dyadicPrimes_union (a : S.integer K) (D : ℝ) :
    dyadicDividingPrimes K S a D ∪ dyadicNondividingPrimes K S a D =
      dyadicSexticPrimeEnvelope K S D := by
  ext p
  simp only [dyadicDividingPrimes, dyadicNondividingPrimes, Finset.mem_union,
    Finset.mem_filter]
  tauto

omit [Finite S] in
theorem dyadicPrimes_disjoint (a : S.integer K) (D : ℝ) :
    Disjoint (dyadicDividingPrimes K S a D) (dyadicNondividingPrimes K S a D) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2

/-- The concrete normalized inverse sum at the actual finite dyadic support. -/
def dyadicSexticInversePolynomial (η : HeckeCharacter K) (u : S.integer K) (D : ℝ) : ℂ :=
  sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (dyadicIdealSupport K D)
    u D sexticDyadicWeight

/-- Exact amplification for the concrete smooth dyadic test and actual finite
ideal supports.  The only hypotheses are the arithmetic data and D > 0.
The envelope and its P/Q split are explicitly constructed, so no arbitrary
support or cover proposition remains in this statement. -/
theorem dyadicSexticInversePolynomial_amplification
    (η : HeckeCharacter K) (a : S.integer K) {D : ℝ} (hD : 0 < D) :
    dyadicSexticInversePolynomial K S ζ hζ σ η 1 D =
      ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
        (moebius (squarefreeIdeal K A).val : ℂ) *
          heckeIdealCoefficient K η (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          dyadicSexticInversePolynomial K S ζ hζ σ η (a ^ 6)
            (D / idealNorm K (squarefreeIdeal K A)) := by
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
    hES hE6 a hP hQ hD sexticDyadicWeight
  · intro I _ ht
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticTerm_primeSupport_subset K S ζ hζ σ η 1 hD le_rfl I ht
  · exact dyadicSexticTerm_eq_zero_of_notMem K S ζ hζ σ η 1 hD
  · intro A _ I _ ht
    rw [dyadicPrimes_union K S a D]
    exact dyadicSexticTerm_primeSupport_subset K S ζ hζ σ η (a ^ 6)
      (div_pos hD (idealNorm_pos K (squarefreeIdeal K A)))
      (div_le_self hD.le (one_le_idealNorm K (squarefreeIdeal K A))) I ht
  · intro A _
    exact dyadicSexticTerm_eq_zero_of_notMem K S ζ hζ σ η (a ^ 6)
      (div_pos hD (idealNorm_pos K (squarefreeIdeal K A)))

end HeckeGeneral.Analysis.SquarefreeAmplification
