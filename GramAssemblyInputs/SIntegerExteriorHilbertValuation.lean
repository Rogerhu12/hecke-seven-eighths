import HeckeGeneral.Arithmetic.SIntegerModulusValuation
import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity

/-! SOURCE ONLY, UNRUN. The upstream normalized finite-place valuation is
the negative multiplicity in the actual exterior contracted ideal.
The canonical-value-group comparison follows the private helper and proof
in pinned PowerResidueReciprocity.lean:55-71,885-1003 (Naganori Yamaguchi,
Apache-2.0); it is restated locally because that helper is private.
No integrality of the S-integer, primary convention, or reciprocity identity
is assumed. This import requires the separately verified full CFT closure. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain
open GlobalClassFieldTheory.Reciprocity
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped Classical nonZeroDivisors

private theorem exterior_canonicalValuation_eq
    {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation R Γ) (x y : R) (hxy : v x = v y) :
    letI : ValuativeRel R := ValuativeRel.ofValuation v
    ValuativeRel.valuation R x = ValuativeRel.valuation R y := by
  let : ValuativeRel R := ValuativeRel.ofValuation v
  change ValuativeRel.ValueGroupWithZero.mk x 1 = ValuativeRel.ValueGroupWithZero.mk y 1
  rw [ValuativeRel.ValueGroupWithZero.mk_eq_mk]
  constructor
  · change v (x * (1 : R)) ≤ v (y * (1 : R))
    simpa only [mul_one] using hxy.le
  · change v (y * (1 : R)) ≤ v (x * (1 : R))
    simpa only [mul_one] using hxy.ge

variable (K : Type) [Field K] [NumberField K]

/-- Equal genuine valuations give equal upstream normalized valuations. -/
theorem finitePlaceNormalizedValuation_eq_of_exterior_valuation_eq
    (p : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (hab : p.valuation K (a : K) = p.valuation K (b : K)) :
    finitePlaceNormalizedValuation K p a = finitePlaceNormalizedValuation K p b := by
  let C := (HeightOneSpectrum.adicAbv K p).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel p
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField p
  let : IsUltrametricDist C := finitePlaceArtinCompletionIsUltrametricDist
    (HeightOneSpectrum.adicAbv K p) (HeightOneSpectrum.isNonarchimedean_adicAbv K p)
  let aC := finitePlaceHilbert_completionUnit K p a
  let bC := finitePlaceHilbert_completionUnit K p b
  have hnorm : ‖(aC : C)‖ = ‖(bC : C)‖ := by
    change ‖algebraMap K C (a : K)‖ = ‖algebraMap K C (b : K)‖
    calc
      _ = HeightOneSpectrum.adicAbv K p (a : K) :=
        AbsoluteValue.completionAbsoluteValue_coe (HeightOneSpectrum.adicAbv K p) (a : K)
      _ = HeightOneSpectrum.adicAbv K p (b : K) := by
        rw [HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def, hab]
      _ = _ :=
        (AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K p) (b : K)).symm
  have hraw : ValuativeRel.valuation C (aC : C) = ValuativeRel.valuation C (bC : C) := by
    apply exterior_canonicalValuation_eq (v := NormedField.valuation (K := C))
    apply NNReal.eq
    simpa only [NormedField.valuation_apply, coe_nnnorm] using hnorm
  change valuationMap C (Additive.ofMul aC) = valuationMap C (Additive.ofMul bC)
  rw [valuationMap_apply, valuationMap_apply]
  unfold IsNonarchimedeanLocalField.v
  congr 2
  exact congrArg (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C) hraw

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The multiplicity is that of the literal contraction, including arbitrary
S-denominators in b. The sign matches the upstream normalized valuation. -/
theorem neg_finitePlaceNormalizedValuation_sInteger_eq_contraction_multiplicity
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (b : NonzeroRingElements (S.integer K)) :
    -finitePlaceNormalizedValuation K p (nonzeroSIntegerFieldUnit K S b) =
      (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K p
        (sIntegerModulusContraction K S b.val) : ℤ) := by
  obtain ⟨d, hd, u, hfield, _hspan⟩ :=
    exists_integer_sUnit_modulus_representative K S b.val b.property
  have hval : p.valuation K (d : K) = p.valuation K (b.val : K) := by
    rw [hfield, map_mul, Set.unit_valuation_eq_one S K u hp, one_mul]
  have hnormalized := finitePlaceNormalizedValuation_eq_of_exterior_valuation_eq K p
    (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit K d hd)
    (nonzeroSIntegerFieldUnit K S b) hval
  have hexp :
      AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K p (Ideal.span {d}) =
        sIntegerModulusPrimeExponents K S b.val b.property p := by
    -- Compare the two actual exponent formulas directly.
    have hform := GlobalClassFieldTheory.Reciprocity.intValuation_eq_exp_neg_idealPrimeMultiplicity K p d hd
    have hproject := sIntegerModulus_valuation K S b.val b.property p hp
    rw [← hval, HeightOneSpectrum.valuation_of_algebraMap, hform] at hproject
    simpa only [WithZero.exp_inj, neg_inj, Nat.cast_inj] using hproject
  have hcontract : sIntegerModulusPrimeExponents K S b.val b.property p =
      AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K p
        (sIntegerModulusContraction K S b.val) := by
    change (UniqueFactorizationMonoid.normalizedFactors (sIntegerModulusContraction K S b.val)).count p.asIdeal = _
    exact (Ideal.count_associates_factors_eq
      (sIntegerModulusContraction_ne_bot K S b.val b.property) p.isPrime p.ne_bot).symm
  rw [← hnormalized, finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit, neg_neg,
    hexp, hcontract]

end HeckeGeneral.Arithmetic
