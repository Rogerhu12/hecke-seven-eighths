import HeckeGeneral.Arithmetic.SIntegerModulus
import HeckeGeneral.Analysis.SIntegerSexticFiniteIdealSum
import HeckeGeneral.Analysis.LocalThetaInput

/-!
Literal consumers of a sixth-power S-unit integral representative.
The representation a,b,u is fixed before the ideal argument. Principal
ideals are compared in O_S, then contracted; no equality of the ordinary
O_K principal ideals and no bound for the ordinary norm of b is asserted.

The ideal symbol, fixed-S/6 zero extension, complete-contraction mask and
actual finite inverse polynomial are preserved. All mathematical inputs
are the existing types and the exact representation equation. The
denominator existence theorem is in Arithmetic.SIntegerSixthPowerDenominator.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton
open HeckeGeneral.Analysis HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (a : S.integer K) (b : 𝓞 K) (u : S.unit K)
variable (hrep : algebraMap (𝓞 K) (S.integer K) b =
  (S.unitEquivUnitsInteger K u).val ^ 6 * a)

include hrep

/-- Only the two principal ideals in the actual S-integer ring coincide. -/
theorem sIntegerPrincipalIdeal_eq_of_sixthPower_sUnit_representative :
    Ideal.span ({algebraMap (𝓞 K) (S.integer K) b} : Set (S.integer K)) =
      Ideal.span ({a} : Set (S.integer K)) := by
  rw [hrep]
  exact Ideal.span_singleton_mul_left_unit
    ((S.unitEquivUnitsInteger K u).isUnit.pow 6) a

/-- Contraction is applied after equality in O_S; ordinary (b) may have
additional prime factors inside S. -/
theorem sIntegerModulusContraction_eq_of_sixthPower_sUnit_representative :
    sIntegerModulusContraction K S (algebraMap (𝓞 K) (S.integer K) b) =
      sIntegerModulusContraction K S a := by
  unfold sIntegerModulusContraction
  rw [sIntegerPrincipalIdeal_eq_of_sixthPower_sUnit_representative K S a b u hrep]

/-- In particular every actual exterior ideal sees the same coprimality
condition, with the representation chosen before that ideal. -/
theorem exteriorIdeal_coprime_contraction_iff_of_sixthPower_sUnit_representative
    (I : ExteriorIdeal K S) :
    IsCoprime I.val.val
        (sIntegerModulusContraction K S (algebraMap (𝓞 K) (S.integer K) b)) ↔
      IsCoprime I.val.val (sIntegerModulusContraction K S a) := by
  rw [sIntegerModulusContraction_eq_of_sixthPower_sUnit_representative K S a b u hrep]

/-- The literal fixed-S/6 deletion together with complete-row coprimality.
No additional moving mask is introduced. This also covers deleted ideals. -/
theorem sexticDeletedCoprimeMask_eq_of_sixthPower_sUnit_representative
    (I : NonzeroIdeal K) :
    (if sexticIdealOutsideS K S I ∧ IsCoprime I.val
        (sIntegerModulusContraction K S (algebraMap (𝓞 K) (S.integer K) b))
      then (1 : ℂ) else 0) =
    (if sexticIdealOutsideS K S I ∧ IsCoprime I.val (sIntegerModulusContraction K S a)
      then (1 : ℂ) else 0) := by
  rw [sIntegerModulusContraction_eq_of_sixthPower_sUnit_representative K S a b u hrep]

end HeckeGeneral.Arithmetic

namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (a : S.integer K) (b : 𝓞 K) (u : S.unit K)
variable (hrep : algebraMap (𝓞 K) (S.integer K) b =
  (S.unitEquivUnitsInteger K u).val ^ 6 * a)
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

include hrep

/-- Fixed exceptional-prime zeros and noncoprimality zeros are retained,
for all nonzero ideals, rather than just for exterior coprime ideals. -/
theorem zeroExtendedSexticIdealEvaluation_eq_of_sixthPower_sUnit_representative
    (I : NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I
        (algebraMap (𝓞 K) (S.integer K) b) =
      zeroExtendedSexticIdealEvaluation K S ζ hζ σ I a := by
  unfold zeroExtendedSexticIdealEvaluation
  split_ifs with hI
  · rw [hrep]
    exact sIntegerSexticIdealEvaluation_mul_sixth_power_unit K S ζ hζ σ I.val
      (nonZeroDivisors.coe_ne_zero I) (fun p hp => (hI p hp).1)
      (fun p hp => (hI p hp).2) u a
  · rfl

/-- One common finite support and one common test are used on both sides.
All original ideal coefficients and zero extensions remain literal. -/
theorem sIntegerSexticInverseIdealPolynomial_eq_of_sixthPower_sUnit_representative
    (η : HeckeCharacter K) (F : Finset (NonzeroIdeal K)) (D : ℝ) (W : ℝ → ℂ) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η F
        (algebraMap (𝓞 K) (S.integer K) b) D W =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η F a D W := by
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro I _hI
  unfold sIntegerSexticInverseIdealTerm
  rw [zeroExtendedSexticIdealEvaluation_eq_of_sixthPower_sUnit_representative
    K S a b u hrep ζ hζ σ I]

end HeckeGeneral.Analysis.SquarefreeAmplification
