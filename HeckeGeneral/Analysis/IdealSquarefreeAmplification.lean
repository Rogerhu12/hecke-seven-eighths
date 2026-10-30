import HeckeGeneral.Arithmetic.IdealMobiusMask
import HeckeGeneral.Analysis.HeckeSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
Exact finite squarefree-ideal decomposition for the single-row amplification.
This is the algebraic identity before row counting or any mean-value bound.
The finite prime envelope must later be chosen to cover the test support.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.IdealMobiusMask HeckeGeneral.Characters
open scoped BigOperators Classical nonZeroDivisors

theorem sum_powerset_disjoint_union {ι : Type*}
    (P Q : Finset ι) (hd : Disjoint P Q) (f : Finset ι → ℂ) :
    (∑ T ∈ (P ∪ Q).powerset, f T) =
      ∑ A ∈ P.powerset, ∑ B ∈ Q.powerset, f (A ∪ B) := by
  induction P using Finset.induction_on generalizing f with
  | empty => simp
  | @insert p P hp ih =>
    have hpQ : p ∉ Q := (Finset.disjoint_insert_left.mp hd).1
    have hd' : Disjoint P Q := (Finset.disjoint_insert_left.mp hd).2
    have hpPQ : p ∉ P ∪ Q := by simp [hp, hpQ]
    rw [Finset.insert_union, Finset.sum_powerset_insert hpPQ,
      Finset.sum_powerset_insert hp]
    rw [ih hd', ih hd']
    simp only [Finset.insert_union]

variable (K : Type*) [Field K] [NumberField K]

/-- The actual nonzero squarefree product of distinct prime ideals. -/
def squarefreeIdeal (T : Finset (HeightOneSpectrum (𝓞 K))) : NonzeroIdeal K :=
  ⟨primeProduct T, mem_nonZeroDivisors_of_ne_zero (primeProduct_ne_bot T)⟩

theorem squarefreeIdeal_union (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hd : Disjoint P Q) :
    squarefreeIdeal K (P ∪ Q) = squarefreeIdeal K P * squarefreeIdeal K Q := by
  apply Subtype.ext
  exact Finset.prod_union hd

theorem idealNorm_squarefree_union (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hd : Disjoint P Q) :
    idealNorm K (squarefreeIdeal K (P ∪ Q)) =
      idealNorm K (squarefreeIdeal K P) * idealNorm K (squarefreeIdeal K Q) := by
  rw [squarefreeIdeal_union K P Q hd]
  simp only [idealNorm, Submonoid.coe_mul, map_mul, Nat.cast_mul]

theorem moebius_squarefree_union (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hd : Disjoint P Q) :
    (UniqueFactorizationMonoid.moebius (squarefreeIdeal K (P ∪ Q)).val : ℂ) =
      (UniqueFactorizationMonoid.moebius (squarefreeIdeal K P).val : ℂ) *
      (UniqueFactorizationMonoid.moebius (squarefreeIdeal K Q).val : ℂ) := by
  simp only [squarefreeIdeal, moebius_primeProduct, Int.cast_pow,
    Finset.card_union_of_disjoint hd, pow_add, Int.cast_mul]

/-- Unnormalised polynomial on all squarefree divisors in an actual finite
prime envelope. No row-dependent mask or extra coefficient is inserted. -/
def squarefreeSum (η : HeckeCharacter K)
    (P : Finset (HeightOneSpectrum (𝓞 K))) (D : ℝ) (W : ℝ → ℂ) : ℂ :=
  ∑ T ∈ P.powerset,
    (UniqueFactorizationMonoid.moebius (squarefreeIdeal K T).val : ℂ) *
      heckeIdealCoefficient K η (squarefreeIdeal K T) *
      W (idealNorm K (squarefreeIdeal K T) / D)

/-- Every squarefree ideal splits uniquely into its factors in P and Q.
The Hecke coefficient and norm are the actual multiplicative functions. -/
theorem squarefreeSum_disjoint_union (η : HeckeCharacter K)
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (hd : Disjoint P Q)
    (D : ℝ) (W : ℝ → ℂ) :
    squarefreeSum K η (P ∪ Q) D W =
      ∑ A ∈ P.powerset,
        (UniqueFactorizationMonoid.moebius (squarefreeIdeal K A).val : ℂ) *
          heckeIdealCoefficient K η (squarefreeIdeal K A) *
          squarefreeSum K η Q (D / idealNorm K (squarefreeIdeal K A)) W := by
  unfold squarefreeSum
  rw [sum_powerset_disjoint_union P Q hd]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hAB : Disjoint A B :=
    hd.mono (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
  rw [moebius_squarefree_union K A B hAB,
    idealNorm_squarefree_union K A B hAB,
    squarefreeIdeal_union K A B hAB, heckeIdealCoefficient_mul]
  rw [div_div_eq_mul_div]
  ring

/-- The D^(-1/2) normalization used by the inverse moment. -/
def squarefreePolynomial (η : HeckeCharacter K)
    (P : Finset (HeightOneSpectrum (𝓞 K))) (D : ℝ) (W : ℝ → ℂ) : ℂ :=
  (Real.sqrt D : ℂ)⁻¹ * squarefreeSum K η P D W

theorem sqrt_scale_amplification {D q : ℝ} (hD : 0 < D) (hq : 0 < q) :
    (Real.sqrt D : ℂ)⁻¹ =
      (Real.sqrt q : ℂ)⁻¹ * (Real.sqrt (D / q) : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul hq.le]
  congr 2
  field_simp

/-- Exact normalised divisor amplification in a finite prime envelope.
Connecting the envelope to the full test support and the remaining sum to
the literal sextic-power row are separate algebraic steps. -/
theorem squarefreePolynomial_disjoint_union (η : HeckeCharacter K)
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (hd : Disjoint P Q)
    {D : ℝ} (hD : 0 < D) (W : ℝ → ℂ) :
    squarefreePolynomial K η (P ∪ Q) D W =
      ∑ A ∈ P.powerset,
        (UniqueFactorizationMonoid.moebius (squarefreeIdeal K A).val : ℂ) *
          heckeIdealCoefficient K η (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          squarefreePolynomial K η Q (D / idealNorm K (squarefreeIdeal K A)) W := by
  unfold squarefreePolynomial
  rw [squarefreeSum_disjoint_union K η P Q hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [sqrt_scale_amplification hD (idealNorm_pos K (squarefreeIdeal K A))]
  ring

end HeckeGeneral.Analysis.SquarefreeAmplification
