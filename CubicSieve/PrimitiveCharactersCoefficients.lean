import CubicSieve.PrimitiveCharacters
import HeckeAxiom.RayCharacter
import DedekindZetaZeroFree.Adeles.Characters.IdelicLocalRestriction
import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveCharacterCofiniteRigidity

/-!
Coefficient and local-type identifications for the constructed primitive ray
characters. All identifications are proved from their actual idelic realization
and exact least conductor. In particular ramified prime zeros are preserved.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace CubicSieve.PrimitiveCharacters

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open DedekindZetaZeroFree DedekindZetaZeroFree.Detector
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.CofinitePrimitiveRigidity
open CubicSieve.CubicCharacters
open scoped Classical NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

private theorem chosenPrime_norm (p : HeightOneSpectrum (𝓞 K)) :
    ‖(_root_.FiniteIdeleGroup.chosenLocalOrderSection p 1).val‖ =
      (residueCard K p : ℝ)⁻¹ := by
  apply localNorm_eq_inv_residueCard_of_valuation K p
  exact Classical.choose_spec
    (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K p
      (WithZero.exp (-1 : ℤ)))

theorem Model.prime_coefficient_eq {hc : NumberField.IsTotallyComplex K}
    {χ : HeckeCharacter K} (P : Model K hc χ) (p : HeightOneSpectrum (𝓞 K)) :
    P.frequency.character p.asIdeal = primeCoefficient K χ p := by
  by_cases hunram : UnramifiedAt K χ p
  · have hnot : ¬ P.frequency.conductor ≤ p.asIdeal := by
      rw [Model.conductor_eq K P]
      intro h
      exact ((HeckeAxiom.conductorIdeal_le_iff K χ p).mp h) hunram
    have hsupp : p ∉ (RayClassBridge.narrowIdealModulus K P.frequency.conductor
        P.frequency.conductor_ne_zero).finitePart.support := by
      simpa only [← Finset.mem_coe, RayClassBridge.narrowIdealModulus_support,
        Set.mem_ofPred_eq] using hnot
    let c := QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup K)
      (_root_.IdeleGroup.finitePrimeIdele p)
    have hr := congrArg (fun z : ℂˣ => (z : ℂ)) (P.realizes c)
    rw [RayClassBridge.ideleClassCharacter_finitePrimeIdele K hc
      P.frequency.conductor P.frequency.conductor_ne_zero P.frequency.character p hsupp] at hr
    calc
      P.frequency.character p.asIdeal = (upstreamCharacter K χ c : ℂ) := hr
      _ = (localComponent K p χ (_root_.FiniteIdeleGroup.chosenLocalOrderSection p 1) : ℂ) := by
        change (upstreamCharacter K χ
          (_root_.IdeleGroup.finitePlaceIdeleClass p
            (_root_.FiniteIdeleGroup.chosenLocalOrderSection p 1)) : ℂ) = _
        rw [upstreamCharacter_local]
        rfl
      _ = primeCoefficient K χ p :=
        (primeCoefficient_eq_of_norm K χ p hunram _ (chosenPrime_norm K p)).symm
  · rw [primeCoefficient_of_ramified K χ p hunram]
    apply (P.frequency.character.eq_zero_iff' p.asIdeal).mpr
    right
    have hm : P.frequency.conductor ≤ p.asIdeal := by
      rw [Model.conductor_eq K P]
      exact (HeckeAxiom.conductorIdeal_le_iff K χ p).mpr hunram
    rw [sup_eq_left.mpr hm]
    exact p.isPrime.ne_top

/-- Equality on every ordinary ideal, including the zero ideal. -/
theorem Model.ideal_coefficient_eq {hc : NumberField.IsTotallyComplex K}
    {χ : HeckeCharacter K} (P : Model K hc χ) (I : Ideal (𝓞 K)) :
    P.frequency.character I = idealCoefficient (primeCoefficient K χ) I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      rw [Ideal.zero_eq_bot, idealCoefficient_zero]
      exact (P.frequency.character.eq_zero_iff' _).mpr (Or.inl rfl)
  | h₂ I hu =>
      rw [isUnit_iff_eq_one.mp hu, idealCoefficient_one]
      simpa only [Ideal.one_eq_top] using P.frequency.character.map_top'
  | h₃ I q hI hq ih =>
      let p : HeightOneSpectrum (𝓞 K) := ⟨q, Ideal.isPrime_of_prime hq, hq.ne_zero⟩
      change P.frequency.character (p.asIdeal * I) =
        idealCoefficient (primeCoefficient K χ) (p.asIdeal * I)
      rw [P.frequency.character.map_mul', idealCoefficient_mul, ih,
        Model.prime_coefficient_eq K P p, idealCoefficient_prime]

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem primitiveCharacter_coefficient (J : ExteriorIdeal K S)
    (I : (Ideal (𝓞 K))⁰) :
    (primitiveCharacter K S D J).character I.val =
      heckeIdealCoefficient K (cubicCharacter K S D J) I := by
  exact Model.ideal_coefficient_eq K
    (model K (totallyComplex K S D) (cubicCharacter K S D J)
      (cubicCharacter_finiteOrder K S D J)) I.val

theorem primitiveCharacter_exterior_coefficient (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (I : ExteriorIdeal K S) :
    (primitiveCharacter K S D J).character I.val.val =
      ExteriorKernel.positiveKernel K S D J I := by
  rw [primitiveCharacter_coefficient, cubicCharacter_idealCoefficient K S D J hJ I]

theorem primitiveCharacter_cube (J : ExteriorIdeal K S) (c : _root_.IdeleClassGroup K) :
    RayClassBridge.ideleClassCharacter K (totallyComplex K S D)
      (primitiveCharacter K S D J).conductor (primitiveCharacter K S D J).conductor_ne_zero
      (primitiveCharacter K S D J).character c ^ 3 = 1 := by
  rw [primitiveCharacter_realizes, upstreamCharacter_apply, ← map_pow]
  have h := congrArg (fun χ : HeckeCharacter K =>
      χ ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K) c))
    (cubicCharacter_pow_three K S D J)
  change cubicCharacter K S D J
    ((_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K) c) ^ 3 = 1 at h
  rw [h, map_one]

/-- The local character satisfies the library's actual principal-law interface. -/
theorem primitiveCharacter_isFrequencyLocalComponent (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) :
    Conductor.Raw.IsFrequencyLocalComponent K (primitiveCharacter K S D J) p
      (localCharacter K S D J p) := by
  exact Conductor.LocalTwistSteps.idelic_restriction_is_raw_local_component K
    (totallyComplex K S D) (primitiveCharacter K S D J) p (localCharacter K S D J p)
    (fun u => (primitiveCharacter_local_component K S D J p u).symm)

/-- Distinct squarefree parameters remain distinct as primitive ideal characters. -/
theorem primitiveCharacter_distinct (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val) (hne : I ≠ J) :
    ¬ samePrimitiveFrequencyCharacter K
      (primitiveCharacter K S D I) (primitiveCharacter K S D J) := by
  intro h
  letI : NumberField.IsTotallyComplex K := totallyComplex K S D
  have hc : (primitiveCharacter K S D I).conductor = (primitiveCharacter K S D J).conductor :=
    primitive_conductors_eq _ _ (fun L _ _ _ => h L)
  have hf : finiteConductor K (cubicCharacter K S D I) =
      finiteConductor K (cubicCharacter K S D J) := by
    apply Subtype.ext
    simpa only [primitiveCharacter_conductor] using hc
  exact hne (CubicConductors.ideal_eq_of_conductor_eq K S D I J hI hJ hf)

end CubicSieve.PrimitiveCharacters
