import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification
import HeckeGeneral.Analysis.SingleRowSeedExponent
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Weighted Cauchy and averaging for the actual dyadic sixth-power identity.
The row majorant, coefficient mass and number of amplifiers remain explicit
antecedents.  No moment estimate, allowed-row count or supremum control is
introduced as an axiom, and none is renamed as the conclusion of MI.
-/

noncomputable section
namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open UniqueFactorizationMonoid
open scoped BigOperators Classical nonZeroDivisors

theorem norm_sum_mul_sq_le_weighted_energy {ι : Type*} (T : Finset ι)
    (c z : ι → ℂ) :
    ‖∑ i ∈ T, c i * z i‖ ^ 2 ≤
      (∑ i ∈ T, ‖c i‖) * ∑ i ∈ T, ‖c i‖ * ‖z i‖ ^ 2 := by
  have htriangle : ‖∑ i ∈ T, c i * z i‖ ≤ ∑ i ∈ T, ‖c i‖ * ‖z i‖ := by
    simpa only [norm_mul] using norm_sum_le T (fun i => c i * z i)
  have hnonneg : 0 ≤ ∑ i ∈ T, ‖c i‖ * ‖z i‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine le_trans ((sq_le_sq₀ (norm_nonneg _) hnonneg).mpr htriangle) ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T
      (fun i _ => norm_nonneg (c i))
      (fun i _ => mul_nonneg (norm_nonneg (c i)) (sq_nonneg ‖z i‖))
  intro i _
  exact le_of_eq (by ring)

theorem norm_sum_mul_sq_le_mass_sq {ι : Type*} (T : Finset ι)
    (c z : ι → ℂ) {B W : ℝ} (hB : 0 ≤ B)
    (hmass : ∑ i ∈ T, ‖c i‖ ≤ W)
    (hrow : ∀ i ∈ T, ‖z i‖ ^ 2 ≤ B) :
    ‖∑ i ∈ T, c i * z i‖ ^ 2 ≤ W ^ 2 * B := by
  have hmass0 : 0 ≤ ∑ i ∈ T, ‖c i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hW : 0 ≤ W := hmass0.trans hmass
  calc
    _ ≤ (∑ i ∈ T, ‖c i‖) * ∑ i ∈ T, ‖c i‖ * ‖z i‖ ^ 2 :=
      norm_sum_mul_sq_le_weighted_energy T c z
    _ ≤ (∑ i ∈ T, ‖c i‖) * ((∑ i ∈ T, ‖c i‖) * B) := by
      apply mul_le_mul_of_nonneg_left _ hmass0
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hrow i hi) (norm_nonneg _)
    _ = (∑ i ∈ T, ‖c i‖) ^ 2 * B := by ring
    _ ≤ W ^ 2 * B := mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hmass0 hW).mpr hmass) hB

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- The exact divisor coefficient occurring in the proved finite identity. -/
def sexticAmplifierCoefficient (η : HeckeCharacter K)
    (A : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  (moebius (squarefreeIdeal K A).val : ℂ) *
    heckeIdealCoefficient K η (squarefreeIdeal K A) *
    (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹

/-- A majorant for every divisor scale of this actual amplifier controls the
single row.  The test, coefficient, support and row a^6 are all the concrete
ones from the previous exact amplification theorem. -/
theorem dyadicSexticInversePolynomial_sq_le
    (η : HeckeCharacter K) (a : S.integer K) {D W B : ℝ} (hD : 0 < D)
    (hB : 0 ≤ B)
    (hmass : ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖sexticAmplifierCoefficient K η A‖ ≤ W)
    (hrow : ∀ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖dyadicSexticInversePolynomial K S ζ hζ σ η (a ^ 6)
        (D / idealNorm K (squarefreeIdeal K A))‖ ^ 2 ≤ B) :
    ‖dyadicSexticInversePolynomial K S ζ hζ σ η 1 D‖ ^ 2 ≤ W ^ 2 * B := by
  rw [dyadicSexticInversePolynomial_amplification K S ζ hζ σ η a hD]
  exact norm_sum_mul_sq_le_mass_sq _ (sexticAmplifierCoefficient K η)
    (fun A => dyadicSexticInversePolynomial K S ζ hζ σ η (a ^ 6)
      (D / idealNorm K (squarefreeIdeal K A))) hB hmass hrow

/-- Summing the same single-row bound over actual amplifiers retains the
full cardinality on the left.  A later injective row map permits a bound
on this majorant sum by the actual MI row energy. -/
theorem dyadicSexticInversePolynomial_average_sq_le
    (η : HeckeCharacter K) (amplifiers : Finset (S.integer K))
    {D W : ℝ} (hD : 0 < D) (B : S.integer K → ℝ)
    (hB : ∀ a ∈ amplifiers, 0 ≤ B a)
    (hmass : ∀ a ∈ amplifiers,
      ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
        ‖sexticAmplifierCoefficient K η A‖ ≤ W)
    (hrow : ∀ a ∈ amplifiers, ∀ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖dyadicSexticInversePolynomial K S ζ hζ σ η (a ^ 6)
        (D / idealNorm K (squarefreeIdeal K A))‖ ^ 2 ≤ B a) :
    (amplifiers.card : ℝ) *
      ‖dyadicSexticInversePolynomial K S ζ hζ σ η 1 D‖ ^ 2 ≤
        W ^ 2 * ∑ a ∈ amplifiers, B a := by
  have h := Finset.sum_le_sum fun a ha =>
    dyadicSexticInversePolynomial_sq_le K S ζ hζ σ η a hD (hB a ha)
      (hmass a ha) (hrow a ha)
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum] using h

/-- The quotient H/P appears only after a positive amplifier count and an
actual summed row majorant have both been supplied. -/
theorem dyadicSexticInversePolynomial_averaging_quotient
    (η : HeckeCharacter K) (amplifiers : Finset (S.integer K))
    {D W P E : ℝ} (hD : 0 < D) (hP : 0 < P)
    (hcount : P ≤ (amplifiers.card : ℝ)) (B : S.integer K → ℝ)
    (hB : ∀ a ∈ amplifiers, 0 ≤ B a)
    (hmass : ∀ a ∈ amplifiers,
      ∑ A ∈ (dyadicDividingPrimes K S a D).powerset,
        ‖sexticAmplifierCoefficient K η A‖ ≤ W)
    (hrow : ∀ a ∈ amplifiers, ∀ A ∈ (dyadicDividingPrimes K S a D).powerset,
      ‖dyadicSexticInversePolynomial K S ζ hζ σ η (a ^ 6)
        (D / idealNorm K (squarefreeIdeal K A))‖ ^ 2 ≤ B a)
    (henergy : ∑ a ∈ amplifiers, B a ≤ E) :
    ‖dyadicSexticInversePolynomial K S ζ hζ σ η 1 D‖ ^ 2 ≤ W ^ 2 * E / P := by
  apply (le_div_iff₀ hP).mpr
  calc
    _ ≤ (amplifiers.card : ℝ) *
        ‖dyadicSexticInversePolynomial K S ζ hζ σ η 1 D‖ ^ 2 := by
      nlinarith [sq_nonneg ‖dyadicSexticInversePolynomial K S ζ hζ σ η 1 D‖]
    _ ≤ W ^ 2 * ∑ a ∈ amplifiers, B a :=
      dyadicSexticInversePolynomial_average_sq_le K S ζ hζ σ η amplifiers
        hD B hB hmass hrow
    _ ≤ W ^ 2 * E := mul_le_mul_of_nonneg_left henergy (sq_nonneg W)

end HeckeGeneral.Analysis.SquarefreeAmplification
