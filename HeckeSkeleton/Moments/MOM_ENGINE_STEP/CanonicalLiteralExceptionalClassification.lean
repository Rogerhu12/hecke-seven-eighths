import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondRectangularFactors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalRows

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
  simp only [OriginalMovingFactors.character, OriginalMovingFactors.singleton,
    Fin.prod_univ_one, zpow_one] <;> rfl

/-- Sixth powers are removed by the existing actual orbit theorem;
this is not an additional law in the primitive interface. -/
theorem elementCharacter_sixth_mul (a b : NonzeroRingElements A.R) :
    elementCharacter P R
      ⟨a.val ^ 6 * b.val, mul_ne_zero (pow_ne_zero 6 a.property) b.property⟩ =
        elementCharacter P R b :=
  congrArg R.character (frequencyBase_sixth_mul K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P a b)

include R in
theorem frequencyBase_ideal_of_generates
    (a : NonzeroRingElements A.R) (I : A.Exterior) (ha : A.Generates I a.val) :
    (frequencyBase K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P
      (Quotient.mk _ a)).ideal.val = sixthPowerFreePart (exteriorMomentIdeal I) := by
  let D := OriginalMovingFactors.singleton (P := P) (R := R) a 1
  have hi := D.factorIdeal_eq_of_generates 0 I ha
  have hi' : (D.decomposition 0).1.val = exteriorMomentIdeal I :=
    congrArg exteriorMomentIdeal hi
  change sixthPowerFreePart (D.decomposition 0).1.val = _
  exact congrArg sixthPowerFreePart hi'

/-- Exterior unramifiedness detects the original full ideal valuation
modulo six, without a cutoff or exceptional predicate. -/
theorem valuation_six_of_unramified (laws : PrimitiveCharacterLaws P R)
    (a : NonzeroRingElements A.R) (I : A.Exterior) (ha : A.Generates I a.val)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hu : UnramifiedAt K (elementCharacter P R a) p) :
    6 ∣ (UniqueFactorizationMonoid.normalizedFactors I.val).count p.asIdeal := by
  have hz : primeExponents (sixthPowerFreePart (exteriorMomentIdeal I)) p = 0 := by
    by_contra hzero
    have hpos := Nat.pos_of_ne_zero hzero
    rw [← frequencyBase_ideal_of_generates P R a I ha] at hpos
    exact laws.ramified _ p hp hpos hu
  rw [primeExponents_sixthPowerFreePart] at hz
  exact Nat.dvd_of_mod_eq_zero hz

theorem elementCharacter_row {Ih : A.Exterior} {h g : A.R} {factor : ℝ}
    (r : ActualChildRow Ih h g factor) :
    elementCharacter P R ⟨r.element, r.generates.1⟩ =
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P R (r.sector P) r.momentIdeal := by
  rw [completeIdealRowCharacter_exterior K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (r.sector P)
      (HeckeAxiom.exteriorEquiv A r.ideal)]
  change R.character (decomposedFrequencyRow K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (r.completeDecomposition P).1 (r.completeDecomposition P).2) = _
  rw [r.completeDecomposition_ideal P] <;> rfl

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
  rw [ActualSecondCorrelationRows.literalCharacter, dif_pos r.val.val.property]
  change (correction * (moving).character) *
    completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν
      (S.extractedRow C r.val.val).momentIdeal = _
  rw [completeIdealRowCharacter_exterior K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν
      (HeckeAxiom.exteriorEquiv A (S.extractedRow C r.val.val).ideal)]

/-- Cancellation is between the same fixed original moving list.
Nothing asserts that its character belongs to theta. -/
theorem same_sixth_base (laws : PrimitiveCharacterLaws P R) (r s : Row)
    (h : S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val =
      S.literalCharacter C P R F oldMoving correction pattern ν s.val.val.val) :
    sixthPowerFreePart (S.extractedRow C r.val.val).momentIdeal =
      sixthPowerFreePart (S.extractedRow C s.val.val).momentIdeal := by
  rw [literalCharacter_explicit P R F oldMoving correction C S pattern ν r,
    literalCharacter_explicit P R F oldMoving correction C S pattern ν s] at h
  exact laws.ideal_faithful _ _ (mul_left_cancel h)

/-- One literal theta class has one internally selected sixth-free
base, including when its original finite row set is empty. -/
theorem exists_class_base (laws : PrimitiveCharacterLaws P R)
    (rows : Finset Row) (θ : HeckeCharacter K) :
    ∃ base : HeckeGeneral.Analysis.NonzeroIdeal K, SixthPowerFreeIdeal base ∧
      ∀ r ∈ rows,
        S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ →
        (S.extractedRow C r.val.val).ideal.val =
          base.val * (sixthPowerAmplifierPart (S.extractedRow C r.val.val).momentIdeal).val ^ 6 := by
  by_cases he : ∃ r ∈ rows,
      S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val = θ
  · obtain ⟨s, hs, hsθ⟩ := he
    refine ⟨sixthPowerFreePart (S.extractedRow C s.val.val).momentIdeal,
      sixthPowerFreePart_isSixthPowerFree _, ?_⟩
    intro r hr hrθ
    have hb := same_sixth_base P R F oldMoving correction C S pattern ν laws r s
      (hrθ.trans hsθ.symm)
    have hf := congrArg (fun I : HeckeGeneral.Analysis.NonzeroIdeal K => I.val)
      (sixthPowerFreePart_mul_amplifier_sixth (S.extractedRow C r.val.val).momentIdeal)
    change (sixthPowerFreePart (S.extractedRow C r.val.val).momentIdeal).val *
      (sixthPowerAmplifierPart (S.extractedRow C r.val.val).momentIdeal).val ^ 6 =
        (S.extractedRow C r.val.val).ideal.val at hf
    rw [hb] at hf
    exact hf.symm
  · refine ⟨sixthPowerFreePart (1 : HeckeGeneral.Analysis.NonzeroIdeal K),
      sixthPowerFreePart_isSixthPowerFree _, ?_⟩
    intro r hr hθ
    exact (he ⟨r, hr, hθ⟩).elim

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
  let a : NonzeroRingElements A.R :=
    ⟨secondActiveFrequencyGenerator C S.primes S.leftMultiplicity S.rightMultiplicity pattern,
      (secondActiveFrequencyGenerator_generates C S.primes
        S.leftMultiplicity S.rightMultiplicity pattern).1⟩
  let b : NonzeroRingElements A.R :=
    ⟨(S.extractedRow C r.val.val).element, (S.extractedRow C r.val.val).generates.1⟩
  let c : NonzeroRingElements A.R :=
    ⟨secondSixthRootGenerator C S.primes S.leftMultiplicity S.rightMultiplicity,
      (secondSixthRootGenerator_generates C S.primes S.leftMultiplicity S.rightMultiplicity).1⟩
  have he : originalElement P C S pattern ν r =
      (⟨c.val ^ 6 * (a.val * b.val),
        mul_ne_zero (pow_ne_zero 6 c.property) (mul_ne_zero a.property b.property)⟩ :
          NonzeroRingElements A.R) := by
    apply Subtype.ext
    change S.frequency r.val.val.val = _
    rw [(S.extractedRow C r.val.val).frequency,
      S.factor_nonunitClass C pattern r.val]
    exact mul_assoc _ _ _
  rw [he, elementCharacter_sixth_mul P R c
    ⟨a.val * b.val, mul_ne_zero a.property b.property⟩, laws.element_mul a b]
  have hr := elementCharacter_row P R (S.extractedRow C r.val.val)
  rw [r.property] at hr
  exact congrArg₂ (fun x y : HeckeCharacter K => x * y)
    (singleton_character P R a).symm hr

/-- The varying factor is the original full frequency character. The
old displayed list and all fixed corrections remain on the same side. -/
theorem literalCharacter_full_frequency (laws : PrimitiveCharacterLaws P R) (r : Row) :
    S.literalCharacter C P R F oldMoving correction pattern ν r.val.val.val =
      (correction * (F.moving P R oldMoving).character) *
        elementCharacter P R (originalElement P C S pattern ν r) := by
  rw [ActualSecondCorrelationRows.literalCharacter, dif_pos r.val.val.property]
  change (correction * (moving).character) *
    completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν
      (S.extractedRow C r.val.val).momentIdeal = _
  rw [(F.moving P R oldMoving).appendSecondFactor_character,
    original_frequency_character P R C S pattern ν laws r]
  ac_rfl

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
  have hprefix : UnramifiedAt K (correction * (F.moving P R oldMoving).character) p :=
    (htheta correction hcorr p hp).mul K
      ((F.moving P R oldMoving).character_unramified p hp hcop)
  have he : (correction * (F.moving P R oldMoving).character) *
      elementCharacter P R (originalElement P C S pattern ν r) = θ.val :=
    (literalCharacter_full_frequency P R F oldMoving correction C S pattern ν laws r).symm.trans hθ
  have hu : UnramifiedAt K (elementCharacter P R (originalElement P C S pattern ν r)) p := by
    apply (unramifiedAt_mul_iff K _ _ p hprefix).mp
    rw [mul_comm, he]
    exact htheta θ.val θ.property p hp
  exact valuation_six_of_unramified P R laws (originalElement P C S pattern ν r)
    (S.originalIdeal r.val.val.val)
    (S.generates r.val.val.val (Finset.mem_filter.mp r.val.val.property).1) p hp hu

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
  unfold FixedChildCharacters.bareFrozenScalar at h
  have h₁ : T.mask B₁.val ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul
      (left_ne_zero_of_mul (left_ne_zero_of_mul h)))
  have h₂ : T.mask B₂.val ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul
      (right_ne_zero_of_mul (left_ne_zero_of_mul h)))
  have hslots : ∏ i ∈ Finset.univ.filter (fun i => i ∉ keep),
      T.mask (frozen i).asIdeal ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have ht := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h) i hi
    exact right_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul ht))
  simpa only [frozenSourceIdeal, map_mul, map_prod, Finset.sdiff_eq_filter,
    Finset.mem_univ, true_and] using mul_ne_zero (mul_ne_zero h₁ h₂) hslots

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
  change ((((if IsCoprime I (oldMoving.support.val * remaining.val) then (1 : ℂ) else 0) *
    (if IsCoprime I F.firstIdeal.val then 1 else 0)) *
    (if IsCoprime I F.poolIdeal.val then 1 else 0)) *
    (if IsCoprime I F.unitIdeal.val then 1 else 0)) *
    (if IsCoprime I extra.val then 1 else 0) ≠ 0 at h
  have hOld : IsCoprime I (oldMoving.support.val * remaining.val) := by
    by_contra hc
    apply h
    simp only [if_neg hc, zero_mul]
  have hFirst : IsCoprime I F.firstIdeal.val := by
    by_contra hc
    apply h
    simp only [if_neg hc, mul_zero, zero_mul]
  have hPool : IsCoprime I F.poolIdeal.val := by
    by_contra hc
    apply h
    simp only [if_neg hc, mul_zero, zero_mul]
  have hUnit : IsCoprime I F.unitIdeal.val := by
    by_contra hc
    apply h
    simp only [if_neg hc, mul_zero, zero_mul]
  exact (F.moving_support_coprime P R oldMoving I).mpr
    ⟨⟨⟨hOld.of_mul_right_left, hFirst⟩, hPool⟩, hUnit⟩

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
  have hm := bareFrozenScalar_mask_ne_zero d.characters b.plainDivisor₁ b.plainDivisor₂
    d.base d.length b.keep b.witness.2 d.slotWeight hscalar
  rw [recipe.characters] at hm
  exact sourceMask_nonzero_coprime P R F parent oldMoving correction remaining extra
    recipe.slots.index _ hm

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
  have hcop := commonScalar_coprime P R F parent oldMoving correction remaining extra
    recipe b hscalar
  rw [hcommon] at hcop
  intro i hi
  have hm : S.leftMultiplicity i = 1 := (Finset.mem_filter.mp hi).2.1
  have hd : (S.primes i).val.asIdeal ∣ (primePowerProduct S.primes S.leftMultiplicity).val := by
    change (S.primes i).val.asIdeal ∣ ∏ j, (S.primes j).val.asIdeal ^ S.leftMultiplicity j
    have hi' := Finset.dvd_prod_of_mem (fun j =>
      (S.primes j).val.asIdeal ^ S.leftMultiplicity j) (Finset.mem_univ i)
    simpa only [hm, pow_one] using hi'
  exact valuation_of_exceptional P R F oldMoving correction C S pattern ν laws
    parent.theta htheta hcorr r θ hθ (S.primes i).val (S.primes i).property
    (hcop.of_isCoprime_of_dvd_left hd)

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
  obtain ⟨base, hfree, hfactor⟩ :=
    exists_class_base P R F oldMoving correction C S pattern ν laws rows θ.val
  refine ⟨base, hfree, ?_, ?_⟩
  · intro r hr hθ
    exact ⟨(sixthPowerAmplifierPart (S.extractedRow C r.val.val).momentIdeal).val,
      hfactor r hr hθ⟩
  · intro r _hr hθ
    exact valuation_class_from_commonScalar P R F parent oldMoving correction hcorr
      remaining extra recipe b C S pattern ν laws htheta hcommon hscalar r θ hθ

end ActualCommonRows

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.valuation_six_of_unramified
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.exists_class_base
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.commonScalar_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalClassification.exists_actual_classification
