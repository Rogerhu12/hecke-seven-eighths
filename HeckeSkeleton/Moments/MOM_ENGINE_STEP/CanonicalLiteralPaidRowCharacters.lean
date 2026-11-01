import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRowCharacters

/-!
# The same ordinary rows after removing an amplifier sixth power

The character attached to an original moving element is computed from
its actual sixth-power-free frequency row, including its unit sector.
Multiplication by a nonzero sixth power preserves that row.  The proof
uses the original orbit relation and uniqueness of the physical
frequency-row/amplifier decomposition; no character extensionality or
unmasked coefficient identity is assumed.

The pool factors of multiplicity one, six and seven therefore have the
same complete Hecke characters as their reduced active factors.  Their
zero-extended ideal evaluations still have the different masks proved
in `CanonicalLiteralPassivePhases`.  This distinction lets the new paid
source retain the original ordinary-row predicate exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

section ActualRows

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

private def sixthDilation (a : NonzeroRingElements (S.integer K))
    (q : ActualSIntegerOrbit K S) : ActualSIntegerOrbit K S :=
  sIntegerOrbitDilation K S (sixthPowerSUnitSubgroup K S)
    ⟨a.val ^ 6, pow_ne_zero 6 a.property⟩ q

/-- Associated generators have identical sixth-power actions on the
actual quotient, even though the generators themselves need not agree. -/
private theorem sixthDilation_eq_of_span
    (a b : NonzeroRingElements (S.integer K))
    (hspan : Ideal.span ({a.val} : Set (S.integer K)) =
      Ideal.span ({b.val} : Set (S.integer K)))
    (q : ActualSIntegerOrbit K S) :
    sixthDilation K S a q = sixthDilation K S b q := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan.symm
  let vS : S.unit K := (S.unitEquivUnitsInteger K).symm v
  have hvS : S.unitEquivUnitsInteger K vS = v :=
    (S.unitEquivUnitsInteger K).apply_symm_apply v
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  apply (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S) _ _).mpr
  refine ⟨⟨vS ^ 6, ⟨vS, rfl⟩⟩, ?_⟩
  have he : (S.unitEquivUnitsInteger K (vS ^ 6)).val * (b.val ^ 6 * x.val) =
      a.val ^ 6 * x.val := by
    rw [map_pow, hvS, Units.val_pow_eq_pow_val]
    rw [← hv, mul_pow]
    ring
  exact congrArg (fun z : S.integer K => (z : K)) he

private theorem sixthDilation_comp
    (a b : NonzeroRingElements (S.integer K)) (q : ActualSIntegerOrbit K S) :
    sixthDilation K S a (sixthDilation K S b q) =
      sixthDilation K S (sIntegerNonzeroMul K S a b) q := by
  refine Quotient.inductionOn q ?_
  intro x
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  change a.val ^ 6 * (b.val ^ 6 * x.val) = (a.val * b.val) ^ 6 * x.val
  rw [mul_pow, mul_assoc]

variable (P : ProbeData K S)

private theorem simultaneousAmplifier_comp (q : ActualSIntegerOrbit K S)
    (I J : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S) :
    actualSimultaneousAmplifier K S P.arithmetic
        (actualSimultaneousAmplifier K S P.arithmetic q I) J =
      actualSimultaneousAmplifier K S P.arithmetic q (exteriorMul K S J I) := by
  change sixthDilation K S ⟨P.arithmetic.generator J, P.arithmetic.generator_ne_zero J⟩
    (sixthDilation K S ⟨P.arithmetic.generator I, P.arithmetic.generator_ne_zero I⟩ q) =
      sixthDilation K S ⟨P.arithmetic.generator (exteriorMul K S J I),
        P.arithmetic.generator_ne_zero (exteriorMul K S J I)⟩ q
  rw [sixthDilation_comp]
  apply sixthDilation_eq_of_span
  change Ideal.span ({P.arithmetic.generator J * P.arithmetic.generator I} :
      Set (S.integer K)) =
    Ideal.span ({P.arithmetic.generator (exteriorMul K S J I)} : Set (S.integer K))
  rw [← Ideal.span_singleton_mul_span_singleton, P.arithmetic.generator_span,
    P.arithmetic.generator_span, P.arithmetic.generator_span, ← Ideal.map_mul] <;> rfl

/-- The actual physical base row used in `OriginalMovingFactors`.
Its unit sector comes from the original orbit equivalence. -/
def frequencyBase (q : ActualSIntegerOrbit K S) : FrequencyRow K S :=
  let x := (exteriorIdealSectorsEquivActualOrbits K S P).symm q
  decomposedFrequencyRow K S x.1 x.2

private def frequencyAmplifier (q : ActualSIntegerOrbit K S) :
    HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S :=
  exteriorSixthPowerAmplifierPart S
    ((exteriorIdealSectorsEquivActualOrbits K S P).symm q).1

private theorem frequencyBase_spec (q : ActualSIntegerOrbit K S) :
    actualSimultaneousAmplifier K S P.arithmetic
        (frequencyRowOrbit K S P (frequencyBase K S P q))
        (frequencyAmplifier K S P q) = q :=
  (exteriorIdealSectorsEquivActualOrbits K S P).apply_symm_apply q

theorem frequencyBase_simultaneousAmplifier (q : ActualSIntegerOrbit K S)
    (I : HeckeGeneral.ThetaSkeleton.ExteriorIdeal K S) :
    frequencyBase K S P (actualSimultaneousAmplifier K S P.arithmetic q I) =
      frequencyBase K S P q := by
  have he : actualSimultaneousAmplifier K S P.arithmetic q I =
      actualSimultaneousAmplifier K S P.arithmetic
        (frequencyRowOrbit K S P (frequencyBase K S P q))
        (exteriorMul K S I (frequencyAmplifier K S P q)) := by
    calc
      _ = actualSimultaneousAmplifier K S P.arithmetic
          (actualSimultaneousAmplifier K S P.arithmetic
            (frequencyRowOrbit K S P (frequencyBase K S P q))
            (frequencyAmplifier K S P q)) I :=
        congrArg (fun v => actualSimultaneousAmplifier K S P.arithmetic v I)
          (frequencyBase_spec K S P q).symm
      _ = _ := simultaneousAmplifier_comp K S P _ _ _
  have hpair := (frequencyRowAmplifierEmbedding K S P).injective
    (a₁ := (frequencyBase K S P (actualSimultaneousAmplifier K S P.arithmetic q I),
      frequencyAmplifier K S P (actualSimultaneousAmplifier K S P.arithmetic q I)))
    (a₂ := (frequencyBase K S P q, exteriorMul K S I (frequencyAmplifier K S P q)))
    ((frequencyBase_spec K S P
      (actualSimultaneousAmplifier K S P.arithmetic q I)).trans he)
  exact congrArg Prod.fst hpair

/-- The sixth power can use any actual nonzero generator.  Its
principal ideal supplies the amplifier, and the unit discrepancy is
removed in the original sixth-unit quotient. -/
theorem frequencyBase_sixth_mul
    (a b : NonzeroRingElements (S.integer K)) :
    frequencyBase K S P (Quotient.mk _
      (⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ :
        NonzeroRingElements (S.integer K))) =
      frequencyBase K S P (Quotient.mk _ b) := by
  let I := actualOrbitExteriorIdeal K S (Quotient.mk _ a)
  have hspan : Ideal.span ({a.val} : Set (S.integer K)) =
      Ideal.span ({P.arithmetic.generator I} : Set (S.integer K)) := by
    rw [P.arithmetic.generator_span]
    change Ideal.span ({a.val} : Set (S.integer K)) =
      (sIntegerModulusContraction K S a.val).map (algebraMap (𝓞 K) (S.integer K))
    exact (map_sIntegerModulusContraction K S a.val).symm
  have he : sixthDilation K S a (Quotient.mk _ b) =
      actualSimultaneousAmplifier K S P.arithmetic (Quotient.mk _ b) I :=
    sixthDilation_eq_of_span K S a
      ⟨P.arithmetic.generator I, P.arithmetic.generator_ne_zero I⟩ hspan _
  exact (congrArg (frequencyBase K S P) he).trans
    (frequencyBase_simultaneousAmplifier K S P _ I)

end ActualRows

open LocalFiniteSums CanonicalLiteralPhaseCalibration CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- A complete Hecke-character identity, obtained by equality of the
actual inputs to the original row-character function. -/
theorem singleton_character_sixth_mul (a b : NonzeroRingElements A.R) (e : ℤ) :
    (OriginalMovingFactors.singleton (P := P) (R := R)
      ⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ e).character =
      (OriginalMovingFactors.singleton (P := P) (R := R) b e).character := by
  simp only [OriginalMovingFactors.character, OriginalMovingFactors.singleton,
    Fin.prod_univ_one]
  apply congrArg (fun χ : HeckeCharacter K => χ ^ e)
  change R.character (frequencyBase K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
      (Quotient.mk _ (⟨a.val ^ 6 * b.val,
        mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ : NonzeroRingElements A.R))) =
    R.character (frequencyBase K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
      (Quotient.mk _ b))
  exact congrArg R.character (frequencyBase_sixth_mul K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P a b)

/-- The original one/six/seven pool factor and the reduced active
factor have the same character, while their deletion masks stay separate. -/
theorem poolMoving_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity)) :
    (F.poolMoving P R).character =
      (CanonicalLiteralPassivePhases.activeMoving P R C p e).character := by
  have hgen := (generator_power_generates C p 2).1
  cases e with
  | one =>
      have he : (⟨F.poolElement, F.pool_generates.1⟩ : NonzeroRingElements A.R) =
          ⟨generator C p ^ 2, hgen⟩ := Subtype.ext hpool
      change (OriginalMovingFactors.singleton (P := P) (R := R)
        ⟨F.poolElement, F.pool_generates.1⟩ 1).character = _
      rw [he] <;> rfl
  | six =>
      have he : (⟨F.poolElement, F.pool_generates.1⟩ : NonzeroRingElements A.R) =
          ⟨(generator C p ^ 2) ^ 6 * 1,
            mul_ne_zero (pow_ne_zero 6 hgen) one_ne_zero⟩ := by
        apply Subtype.ext
        rw [hpool, mul_one, ← pow_mul] <;> rfl
      change (OriginalMovingFactors.singleton (P := P) (R := R)
        ⟨F.poolElement, F.pool_generates.1⟩ 1).character = _
      rw [he]
      exact singleton_character_sixth_mul P R
        ⟨generator C p ^ 2, hgen⟩ ⟨1, one_ne_zero⟩ 1
  | seven =>
      have he : (⟨F.poolElement, F.pool_generates.1⟩ : NonzeroRingElements A.R) =
          ⟨(generator C p ^ 2) ^ 6 * generator C p ^ 2,
            mul_ne_zero (pow_ne_zero 6 hgen) hgen⟩ := by
        apply Subtype.ext
        rw [hpool, ← pow_mul, ← pow_add] <;> rfl
      change (OriginalMovingFactors.singleton (P := P) (R := R)
        ⟨F.poolElement, F.pool_generates.1⟩ 1).character = _
      rw [he]
      exact singleton_character_sixth_mul P R
        ⟨generator C p ^ 2, hgen⟩ ⟨generator C p ^ 2, hgen⟩ 1

theorem moving_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) :
    (F.moving P R oldMoving).character =
      ((reducedPhases F C p e).moving P R oldMoving).character := by
  rw [FixedPhases.moving_character, FixedPhases.moving_character,
    poolMoving_character P R F C p e hpool, reducedPhases_poolMoving] <;> rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem appended_character (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool) :
    ((F.moving P R oldMoving).appendSecondFactor C primes m n pattern).character =
      (((reducedPhases F C p e).moving P R oldMoving).appendSecondFactor
        C primes m n pattern).character := by
  simp only [OriginalMovingFactors.appendSecondFactor_character,
    moving_character P R F C p e hpool oldMoving]

theorem rowCharacter_eq (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (primes : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C primes m n
        pattern ν u =
      CanonicalLiteralAllocatedData.rowCharacter P R (reducedPhases F C p e)
        oldMoving correction C primes m n pattern ν u := by
  unfold CanonicalLiteralAllocatedData.rowCharacter
  rw [appended_character P R F C p e hpool]

theorem literalCharacter_eq {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)
    (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern ν h =
      S.literalCharacter C P R (reducedPhases F C p e) oldMoving correction pattern ν h := by
  unfold ActualSecondCorrelationRows.literalCharacter
  split_ifs with hh
  · exact rowCharacter_eq P R F C p e hpool oldMoving correction S.primes
      S.leftMultiplicity S.rightMultiplicity pattern ν _
  · rfl

/-- The original ordinary filter is unchanged before any passive
allocation or normalized child is selected. -/
theorem ordinary_iff {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)
    (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (theta : Finset (HeckeCharacter K)) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern ν h ∉ theta ↔
      S.literalCharacter C P R (reducedPhases F C p e) oldMoving correction pattern ν h ∉ theta := by
  rw [literalCharacter_eq P R S F C p e hpool oldMoving correction pattern ν h]

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.frequencyBase_sixth_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.singleton_character_sixth_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.poolMoving_character
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.appended_character
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.literalCharacter_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidRowCharacters.ordinary_iff
