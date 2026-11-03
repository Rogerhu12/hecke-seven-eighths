import CubicSieve.ExteriorKernel
import ArithmeticFrequencyRowRamification
import HeckeGeneral.Characters.SexticTameConductor

/-!
# Actual cubic Kummer Hecke characters

The character attached to J is the square of the arithmetic sextic Kummer
character of one integral representative of generator(J), in its original
sixth-power S-unit class. Its embedding and root orientation are those of D.
The coefficient at I is therefore the literal TRANSPOSE kernel (J,I).

For arbitrary J the good-prime statements require the displayed coprimality
condition. For squarefree J, the post-square ramification is proved below,
so the final whole-ideal calibration includes the actual ramified zeros.
No large sieve estimate, global primitivity theorem, or uniform bound for
the conductor at the primes in S is asserted here.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace CubicSieve.CubicCharacters

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

private theorem primeCoefficient_square_of_unramified (χ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hχ : UnramifiedAt K χ p) :
    primeCoefficient K (χ ^ 2) p = primeCoefficient K χ p ^ 2 := by
  have hχ₂ : UnramifiedAt K (χ ^ 2) p := by
    simpa only [pow_two] using hχ.mul K hχ
  rw [primeCoefficient_of_unramified K _ p hχ₂,
    primeCoefficient_of_unramified K _ p hχ]
  change ((localComponent K p χ (localUniformizerUnit K p) ^ 2 : Circle) : ℂ) = _
  exact Circle.coe_pow _ _

local instance cubicResidueField (p : HeightOneSpectrum (𝓞 K)) :
    Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _

local instance cubicResidueFintype (p : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _

/-- Squaring a sextic Kummer character still ramifies when its signed
radicand valuation is not divisible by three. This proves the necessary
post-square assertion; ramification of the sextic character alone is insufficient. -/
theorem square_kummer_not_unramified_of_valuation
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (embedding : K →+* ℂ)
    (a : Kˣ) (p : HeightOneSpectrum (𝓞 K)) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (hval : ¬ (3 : ℤ) ∣ finitePlaceNormalizedValuation K p a) :
    ¬ UnramifiedAt K
      ((arithmeticSexticKummerCharacter K embedding
        ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩ a) ^ 2) p := by
  intro hunram
  let F := 𝓞 K ⧸ p.asIdeal
  let h6 := six_dvd_card_residue_sub_one K ζ hζ p hp6
  let ζF := sexticResidueRootUnit K ζ hζ p
  let ζC := sexticComplexRootUnit K ζ hζ embedding
  let hF := isPrimitiveRoot_sexticResidueRootUnit K ζ hζ p hp6
  let hC := isPrimitiveRoot_sexticComplexRootUnit K ζ hζ embedding
  obtain ⟨u, hu⟩ :=
    HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.exists_unitCharacter_order_six
      F h6 ζF ζC hF hC
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : F)
  have hxp : x ∉ p.asIdeal := by
    intro hxmem
    have hz : Ideal.Quotient.mk p.asIdeal x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hxmem
    exact u.ne_zero (hx.symm.trans hz)
  let c : ℂˣ := HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.unitCharacter
    F h6 ζF ζC hF hC u
  have hc : orderOf c = 6 := hu
  have heval : sexticResidueEvaluation K ζ hζ embedding p hp6 x = (c : ℂ) := by
    change HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.character F h6 ζF ζC hF hC
      (Ideal.Quotient.mk p.asIdeal x) = (c : ℂ)
    rw [hx]
    exact HeckeGeneral.Arithmetic.FiniteFieldSexticCharacter.character_unit F h6 ζF ζC hF hC u
  have hl := arithmeticSexticKummerCharacter_localComponent_primeUnit_zpow
    K ζ hζ embedding a p hp6 x hxp
  rw [heval] at hl
  have hone := congrArg (fun z : Circle => (z : ℂ))
    (hunram _ (primeAvoidingIntegralFieldUnit_local_norm_one K p x hxp))
  change ((localComponent K p
      (arithmeticSexticKummerCharacter K embedding
        ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩ a)
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom
        (primeAvoidingIntegralFieldUnit K p x hxp)) ^ 2 : Circle) : ℂ) = 1 at hone
  rw [Circle.coe_pow, hl] at hone
  have hpow : c ^ (finitePlaceNormalizedValuation K p a * 2) = 1 := by
    apply Units.ext
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      Units.val_one, zpow_mul, zpow_ofNat] using hone
  have hdvd : (6 : ℤ) ∣ finitePlaceNormalizedValuation K p a * 2 := by
    simpa only [hc, Nat.cast_ofNat] using (orderOf_dvd_iff_zpow_eq_one.mpr hpow)
  obtain ⟨k, hk⟩ := hdvd
  apply hval
  exact ⟨k, by omega⟩

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- A single representative is chosen before any prime or evaluation ideal. -/
def integralRepresentative (J : ExteriorIdeal K S) :
    {b : 𝓞 K // b ≠ 0 ∧ ∃ u : S.unit K,
      algebraMap (𝓞 K) (S.integer K) b =
        (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator J} := by
  have h : ∃ b : 𝓞 K, b ≠ 0 ∧ ∃ u : S.unit K,
      algebraMap (𝓞 K) (S.integer K) b =
        (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator J := by
    obtain ⟨b, hb, u, hrep⟩ := exists_integer_sixthPower_sUnit_representative
      K S (D.generator J) (D.generator_ne_zero J)
    exact ⟨b, hb, u, hrep⟩
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

def sexticCharacter (J : ExteriorIdeal K S) : HeckeCharacter K :=
  let b := integralRepresentative K S D J
  arithmeticSexticKummerCharacter K D.embedding
    ⟨D.root6, (mem_primitiveRoots (by norm_num)).mpr D.primitive6⟩
    (nonzeroIntegralFieldUnit K b.val b.property.1)

def cubicCharacter (J : ExteriorIdeal K S) : HeckeCharacter K :=
  sexticCharacter K S D J ^ 2

theorem sexticCharacter_pow_six (J : ExteriorIdeal K S) :
    sexticCharacter K S D J ^ 6 = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  change sexticCharacter K S D J x ^ 6 = 1
  dsimp only [sexticCharacter]
  exact arithmeticSexticKummerCharacter_pow K _ _ _ x

/-- Order divides three; the unit ideal is not asserted to give exact order three. -/
theorem cubicCharacter_pow_three (J : ExteriorIdeal K S) :
    cubicCharacter K S D J ^ 3 = 1 := by
  rw [cubicCharacter, ← pow_mul, show (2 * 3 : ℕ) = 6 by decide,
    sexticCharacter_pow_six]

theorem cubicCharacter_finiteOrder (J : ExteriorIdeal K S) :
    FiniteOrder (cubicCharacter K S D J) := by
  apply (finiteOrder_iff_pointwise _).mpr
  refine ⟨3, by decide, fun x => ?_⟩
  simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using
    congrArg (fun χ : HeckeCharacter K => χ x) (cubicCharacter_pow_three K S D J)

theorem sexticCharacter_unramifiedAt (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (hpJ : ¬ p.asIdeal ∣ J.val.val) :
    UnramifiedAt K (sexticCharacter K S D J) p := by
  let b := integralRepresentative K S D J
  obtain ⟨u, hrep⟩ := b.property.2
  exact arithmeticSexticKummerCharacter_integer_representative_unramifiedAt
    K S D.embedding ⟨D.root6, (mem_primitiveRoots (by norm_num)).mpr D.primitive6⟩
    (D.generator J) (D.generator_ne_zero J) b.val b.property.1 u hrep p hp
    (by simpa only [contraction_thetaGenerator] using hpJ) (D.away_six p hp)

theorem cubicCharacter_unramifiedAt (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (hpJ : ¬ p.asIdeal ∣ J.val.val) :
    UnramifiedAt K (cubicCharacter K S D J) p := by
  simpa only [cubicCharacter, pow_two] using
    (sexticCharacter_unramifiedAt K S D J p hp hpJ).mul K
      (sexticCharacter_unramifiedAt K S D J p hp hpJ)

theorem sexticCharacter_primeCoefficient (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (hpJ : ¬ p.asIdeal ∣ J.val.val) :
    primeCoefficient K (sexticCharacter K S D J) p =
      sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
        (D.away_six p hp) (D.generator J) := by
  let b := integralRepresentative K S D J
  obtain ⟨u, hrep⟩ := b.property.2
  exact arithmeticSexticKummerCharacter_primeCoefficient_sInteger K S D
    (D.generator J) (D.generator_ne_zero J) b.val b.property.1 u hrep p hp
    (by simpa only [contraction_thetaGenerator] using hpJ)

theorem cubicCharacter_primeCoefficient_of_not_dvd (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (hpJ : ¬ p.asIdeal ∣ J.val.val) :
    primeCoefficient K (cubicCharacter K S D J) p =
      sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
        (D.away_six p hp) (D.generator J) ^ 2 := by
  rw [cubicCharacter, primeCoefficient_square_of_unramified K _ p
    (sexticCharacter_unramifiedAt K S D J p hp hpJ),
    sexticCharacter_primeCoefficient K S D J p hp hpJ]

/-- Denominator clearing changes no exterior multiplicity. -/
theorem integralRepresentative_multiplicity (J : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    idealPrimeMultiplicity K p (Ideal.span {(integralRepresentative K S D J).val}) =
      primeExponents J.val p := by
  let b := integralRepresentative K S D J
  obtain ⟨u, hrep⟩ := b.property.2
  let I := nonzeroIntegralPrincipalIdeal K b.val b.property.1
  have hmap : I.val.map (algebraMap (𝓞 K) (S.integer K)) =
      Ideal.span ({algebraMap (𝓞 K) (S.integer K) b.val} : Set (S.integer K)) := by
    change (Ideal.span ({b.val} : Set (𝓞 K))).map _ = _
    rw [Ideal.map_span, Set.image_singleton]
  have hcontract : sIntegerModulusContraction K S
      (algebraMap (𝓞 K) (S.integer K) b.val) = (outsideSIdeal K S I).val := by
    unfold sIntegerModulusContraction
    rw [← hmap]
    exact under_map_ideal_eq_outsideSIdeal K S I
  have hsame : outsideSIdeal K S I = J.val := by
    apply Subtype.ext
    exact hcontract.symm.trans
      ((sIntegerModulusContraction_eq_of_sixthPower_sUnit_representative
        K S (D.generator J) b.val u hrep).trans (contraction_thetaGenerator K S D J))
  have hexp := congrArg (fun I : NonzeroIdeal K => primeExponents I p) hsame
  rw [outsideSIdeal, primeExponents_idealOfPrimeExponents, outsideSPrimeExponents,
    Finsupp.filter_apply_pos (fun p => p ∉ S) _ hp] at hexp
  exact (idealPrimeMultiplicity_eq_primeExponents K I p).trans hexp

/-- A squarefree radicand has local cubic order three at each exterior divisor. -/
theorem cubicCharacter_not_unramifiedAt_of_dvd (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpJ : p.asIdeal ∣ J.val.val) :
    ¬ UnramifiedAt K (cubicCharacter K S D J) p := by
  let b := integralRepresentative K S D J
  have hcount : primeExponents J.val p ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero J.val)).mp hJ)
      p.asIdeal
  have hne : primeExponents J.val p ≠ 0 := by
    rw [← idealPrimeMultiplicity_eq_primeExponents K J.val p]
    exact (Associates.count_ne_zero_iff_dvd
      (nonZeroDivisors.coe_ne_zero J.val) p.irreducible).mpr hpJ
  have hone : primeExponents J.val p = 1 := by omega
  apply square_kummer_not_unramified_of_valuation K D.root6 D.primitive6 D.embedding
    (nonzeroIntegralFieldUnit K b.val b.property.1) p (D.away_six p hp)
  rw [finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit,
    integralRepresentative_multiplicity K S D J p hp, hone]
  norm_num

/-- The exact tame conductor exponent is proved for the squared character. -/
theorem cubicCharacter_localConductorExponent (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    localConductorExponent K (cubicCharacter K S D J) p =
      if p.asIdeal ∣ J.val.val then 1 else 0 := by
  have h6 : cubicCharacter K S D J ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul, cubicCharacter_pow_three, one_pow]
  have hu := localConductorExponent_le_one_of_pow_six_eq_one K
    (cubicCharacter K S D J) h6 p (D.away_six p hp)
  by_cases hdiv : p.asIdeal ∣ J.val.val
  · rw [ite_eq_left hdiv]
    have hn : localConductorExponent K (cubicCharacter K S D J) p ≠ 0 := by
      intro hz
      exact cubicCharacter_not_unramifiedAt_of_dvd K S D J hJ p hp hdiv
        ((localConductorExponent_eq_zero_iff K _ p).mp hz)
    omega
  · rw [ite_eq_right hdiv]
    exact (localConductorExponent_eq_zero_iff K _ p).mpr
      (cubicCharacter_unramifiedAt K S D J p hp hdiv)

/-- Every exterior prime coefficient is calibrated, including actual ramified zeros. -/
theorem cubicCharacter_primeCoefficient (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    primeCoefficient K (cubicCharacter K S D J) p =
      sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
        (D.away_six p hp) (D.generator J) ^ 2 := by
  by_cases hdiv : p.asIdeal ∣ J.val.val
  · rw [primeCoefficient_of_ramified K _ p
      (cubicCharacter_not_unramifiedAt_of_dvd K S D J hJ p hp hdiv)]
    have hz : sIntegerSexticResidueMap K S p hp (D.generator J) = 0 := by
      apply (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hp _).mpr
      simpa only [contraction_thetaGenerator] using hdiv
    simp only [sIntegerSexticEvaluation, hz, sexticResidueCharacter_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · exact cubicCharacter_primeCoefficient_of_not_dvd K S D J p hp hdiv

/-- No mask is inserted: ramified prime coefficients supply the genuine zeros.
The transpose (J,I) retains the Kummer root orientation. -/
theorem cubicCharacter_idealCoefficient (J : ExteriorIdeal K S)
    (hJ : Squarefree J.val.val) (I : ExteriorIdeal K S) :
    heckeIdealCoefficient K (cubicCharacter K S D J) I.val =
      ExteriorKernel.positiveKernel K S D J I := by
  letI : Fintype (idealPrimeDivisors K I.val.val) :=
    (idealPrimeDivisors_finite K I.val.val (nonZeroDivisors.coe_ne_zero I.val)).fintype
  change idealCoefficient (primeCoefficient K (cubicCharacter K S D J)) I.val.val =
    (idealSymbol K S D I (D.generator J)) ^ (2 : ℕ)
  rw [idealCoefficient_eq_prod_idealPrimeDivisors K _ I.val]
  simp only [idealSymbol, sIntegerSexticIdealEvaluation]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [cubicCharacter_primeCoefficient K S D J hJ p.val (I.property p.val p.property)]
  simp only [← pow_mul, Nat.mul_comm]

end CubicSieve.CubicCharacters
