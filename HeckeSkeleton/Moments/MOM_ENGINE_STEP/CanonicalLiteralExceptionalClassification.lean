import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondRectangularFactors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalRows

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Original character arithmetic and the actual exceptional sixth classes

The cross-task arithmetic input concerns the original row-character map
only. It is stated before a moment datum, a theta family, moving factors,
an extracted source, or a norm cutoff is supplied. Its three assertions
are Kummer multiplicativity, faithfulness on the sixth-free ideal, and
ramification at an exterior prime with nonzero sixth-free exponent.
No actual-row classification, fixed base ideal, or counting estimate is
an input.

The same actual theta class cancels its fixed moving prefix. Faithfulness
then identifies the sixth-free parts of its literal residual ideals.
The complete frequency is reconstructed before applying ramification;
its removed sixth power is discarded only in the character, not in the
source mask. Finally the actual frozen scalar proves that every genuine
second common prime avoids the old displayed moving support.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralPaidRowCharacters CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The character is computed from the same original element, probe,
and supplied calibrated row-character function. -/
def elementCharacter (a : NonzeroRingElements A.R) : HeckeCharacter K :=
  R.character (frequencyBase K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
    (Quotient.mk _ a))

/-- Primitive global arithmetic laws, independent of all moment data.
These are the statements supplied by the original Kummer constructor,
its global uniqueness, and its exterior-prime ramification theorem. -/
structure PrimitiveCharacterLaws : Prop where
  ideal_faithful : ∀ u v : FrequencyRow K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
    R.character u = R.character v → u.ideal.val = v.ideal.val
  element_mul : ∀ a b : NonzeroRingElements A.R,
    elementCharacter P R ⟨a.val * b.val, mul_ne_zero a.property b.property⟩ =
      elementCharacter P R a * elementCharacter P R b
  ramified : ∀ (u : FrequencyRow K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (p : HeightOneSpectrum (𝓞 K)), p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) →
    0 < primeExponents u.ideal.val p → ¬ UnramifiedAt K (R.character u) p

theorem singleton_character (a : NonzeroRingElements A.R) :
    (OriginalMovingFactors.singleton (P := P) (R := R) a 1).character =
      elementCharacter P R a := by
  sorry

/-- Sixth powers are removed by the existing actual orbit theorem;
this is not an additional law in the primitive interface. -/
theorem elementCharacter_sixth_mul (a b : NonzeroRingElements A.R) :
    elementCharacter P R
      ⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ =
        elementCharacter P R b := by
  sorry

include R in
theorem frequencyBase_ideal_of_generates
    (a : NonzeroRingElements A.R) (I : A.Exterior) (ha : A.Generates I a.val) :
    (frequencyBase K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
      (Quotient.mk _ a)).ideal.val = sixthPowerFreePart (exteriorMomentIdeal I) := by
  sorry

/-- Exterior unramifiedness detects the original full ideal valuation
modulo six, without a cutoff or exceptional predicate. -/
theorem valuation_six_of_unramified (laws : PrimitiveCharacterLaws P R)
    (a : NonzeroRingElements A.R) (I : A.Exterior) (ha : A.Generates I a.val)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hu : UnramifiedAt K (elementCharacter P R a) p) :
    6 ∣ (UniqueFactorizationMonoid.normalizedFactors I.val).count p.asIdeal := by
  sorry

theorem elementCharacter_row {Ih : A.Exterior} {h g : A.R} {factor : ℝ}
    (r : ActualChildRow Ih h g factor) :
    elementCharacter P R ⟨r.element, r.generates.1⟩ =
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P R (r.sector P) r.momentIdeal := by
  sorry

section ActualRows

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

local notation "Row" => PatternSector P S C pattern ν
local notation "moving" => (F.moving P R oldMoving).appendSecondFactor C
  S.primes S.leftMultiplicity S.rightMultiplicity pattern

theorem literalCharacter_explicit (r : Row) :
    S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val =
      (correction * (moving).character) *
        R.character (decomposedFrequencyRow K
          (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (HeckeAxiom.exteriorEquiv A (S.extractedRow C r.val.val).ideal) ν) := by
  sorry

/-- Cancellation is between the same fixed original moving list.
Nothing asserts that its character belongs to theta. -/
theorem same_sixth_base (laws : PrimitiveCharacterLaws P R) (r s : Row)
    (h : S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val =
      S.literalCharacter C P R F oldMoving correction pattern ν s.val.val.val) :
    sixthPowerFreePart (S.extractedRow C r.val.val).momentIdeal =
      sixthPowerFreePart (S.extractedRow C s.val.val).momentIdeal := by
  sorry

/-- One literal theta class has one internally selected sixth-free
base, including when its original finite row set is empty. -/
theorem exists_class_base (laws : PrimitiveCharacterLaws P R)
    (rows : Finset Row) (θ : HeckeCharacter K) :
    ∃ base : HeckeGeneral.Analysis.NonzeroIdeal K, SixthPowerFreeIdeal base ∧
      ∀ r ∈ rows,
        S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ →
        (S.extractedRow C r.val.val).ideal.val =
          base.val * (sixthPowerAmplifierPart (S.extractedRow C r.val.val).momentIdeal).val ^ 6 := by
  sorry

/-- The nonzero proof comes from the same original row membership. -/
def originalElement (r : Row) : NonzeroRingElements A.R :=
  ⟨S.frequency r.val.val.val,
    (S.generates r.val.val.val (Finset.mem_filter.mp r.val.val.property).1).1⟩

/-- Exact reconstruction uses the actual gcd/nonunit factor and removes
its sixth power only through the proved frequency-base identity. -/
theorem original_frequency_character (laws : PrimitiveCharacterLaws P R) (r : Row) :
    elementCharacter P R (originalElement P C S pattern ν r) =
      (secondOriginalMovingFactors P R C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern).character *
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν
          (S.extractedRow C r.val.val).momentIdeal := by
  sorry

/-- The varying factor is the original full frequency character. The
old displayed list and all fixed corrections remain on the same side. -/
theorem literalCharacter_full_frequency (laws : PrimitiveCharacterLaws P R) (r : Row) :
    S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val =
      (correction * (F.moving P R oldMoving).character) *
        elementCharacter P R (originalElement P C S pattern ν r) := by
  sorry

/-- Only the original fixed family's conductor condition is used.
There is no closure assumption on that family. -/
theorem valuation_of_exceptional (laws : PrimitiveCharacterLaws P R)
    (theta : Finset (HeckeCharacter K))
    (htheta : ∀ θ ∈ theta, ∀ p : HeightOneSpectrum (𝓞 K),
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) → UnramifiedAt K θ p)
    (hcorr : correction ∈ theta) (r : Row) (θ : theta)
    (hθ : S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ.val)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (F.moving P R oldMoving).support.val) :
    6 ∣ (UniqueFactorizationMonoid.normalizedFactors
      (S.originalIdeal r.val.val.val).val).count p.asIdeal := by
  sorry

end ActualRows

section OriginalFrozenMask

/-- Nonzero original frozen atoms preserve every factor of the actual
common mask, including those from frozen prime occurrences. -/
theorem bareFrozenScalar_mask_ne_zero {k : ℕ} (T : FixedChildCharacters K k)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal K) (Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 K))
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (h : T.bareFrozenScalar B₁ B₂ Z length keep frozen w ≠ 0) :
    T.mask (frozenSourceIdeal B₁ B₂ keep frozen) ≠ 0 := by
  sorry

variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The literal source mask itself yields the full fixed moving
support condition; no primitive-character conductor inference is used. -/
theorem sourceMask_nonzero_coprime {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) (I : Ideal (𝓞 K))
    (h : (CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving
      correction remaining extra index).mask I ≠ 0) :
    IsCoprime I (F.moving P R oldMoving).support.val := by
  sorry

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

include recipe in
/-- This is the original common scalar before the exceptional split.
The whole frozen common ideal, with all multiplicities, avoids the
displayed prefix whenever that actual scalar is nonzero. -/
theorem commonScalar_coprime (hscalar : d.commonScalar b ≠ 0) :
    IsCoprime (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)
      (F.moving P R oldMoving).support.val := by
  sorry

end OriginalFrozenMask

section ActualCommonRows

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

local notation "Row" => PatternSector P S C pattern ν

include recipe hcorr

/-- The common-ideal equality is the original atlas product identity.
The nonzero scalar is its actual frozen coefficient, not an assumption
on the derived exceptional count or a primitive character conductor. -/
theorem valuation_class_from_commonScalar (laws : PrimitiveCharacterLaws P R)
    (htheta : ∀ θ ∈ parent.theta, ∀ p : HeightOneSpectrum (𝓞 K),
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) → UnramifiedAt K θ p)
    (hcommon : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 =
      (primePowerProduct S.primes S.leftMultiplicity).val)
    (hscalar : d.commonScalar b ≠ 0) (r : Row) (θ : parent.theta)
    (hθ : S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ.val) :
    ∀ i ∈ multiplicityOneNonunitPrimes C S.primes S.leftMultiplicity
      S.rightMultiplicity (S.frequency r.val.val.val),
      6 ∣ (UniqueFactorizationMonoid.normalizedFactors
        (S.originalIdeal r.val.val.val).val).count (S.primes i).val.asIdeal := by
  sorry

/-- Both arithmetic fields required by the existing actual exceptional
count are conclusions for the same literal theta class. The witness
factor is always the actual ideal's sixth-power amplifier part. -/
theorem exists_actual_classification (laws : PrimitiveCharacterLaws P R)
    (htheta : ∀ θ ∈ parent.theta, ∀ p : HeightOneSpectrum (𝓞 K),
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) → UnramifiedAt K θ p)
    (hcommon : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 =
      (primePowerProduct S.primes S.leftMultiplicity).val)
    (hscalar : d.commonScalar b ≠ 0) (rows : Finset Row) (θ : parent.theta) :
    ∃ base : HeckeGeneral.Analysis.NonzeroIdeal K, SixthPowerFreeIdeal base ∧
      (∀ r ∈ rows,
        S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ.val →
        ∃ a : Ideal (𝓞 K), (S.extractedRow C r.val.val).ideal.val = base.val * a ^ 6) ∧
      (∀ r ∈ rows,
        S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ.val →
        ∀ i ∈ multiplicityOneNonunitPrimes C S.primes S.leftMultiplicity
          S.rightMultiplicity (S.frequency r.val.val.val),
          6 ∣ (UniqueFactorizationMonoid.normalizedFactors
            (S.originalIdeal r.val.val.val).val).count (S.primes i).val.asIdeal) := by
  sorry

end ActualCommonRows

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.valuation_six_of_unramified
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.exists_class_base
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.commonScalar_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.exists_actual_classification
