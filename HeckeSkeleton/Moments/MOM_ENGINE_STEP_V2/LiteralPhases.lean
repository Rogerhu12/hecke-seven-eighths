import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PatternRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RemainingMaskRadical
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAtlas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SectorRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonScalarReweight

set_option linter.unusedSectionVars false

/-!
# Append the actual second factor to every original moving factor

The finite list is concatenated with `Fin.append`. Every old element and
integer exponent remains in its original coordinate, including zero or
cancelling exponents. Its computed character is multiplied by the actual
second active character, and its displayed prime support is the union
of the two original supports.

The original remaining mask is first replaced by its proved exterior
radical, behind the unchanged complete-row gate. The complete sixth root
is then multiplied into that remaining ideal. Individual support atoms
for both lists are constructed internally from their actual generators;
the old ideal is the genuine effective full support of the old list.
No completed support divisibility or child-row bound is an input.

The last declarations apply the original physical second-row window to
the appended list on the fixed original nonunit pattern. Thus the same
canonical child retains the old moving character and all its zeros,
the new active factor and the complete sixth-root deletion.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

namespace OriginalMovingFactors

/-- Literal concatenation of the original element and exponent lists. -/
def appendFactors (D E : OriginalMovingFactors A P Rchar) :
    OriginalMovingFactors A P Rchar where
  count := D.count + E.count
  element := Fin.append D.element E.element
  power := Fin.append D.power E.power

variable (D E : OriginalMovingFactors A P Rchar)

@[simp] theorem appendFactors_count : ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).count = D.count + E.count := rfl

@[simp] theorem appendFactors_element_left (i : Fin D.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).element (Fin.castAdd E.count i) = D.element i := by
  sorry

@[simp] theorem appendFactors_element_right (i : Fin E.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).element (Fin.natAdd D.count i) = E.element i := by
  sorry

@[simp] theorem appendFactors_power_left (i : Fin D.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).power (Fin.castAdd E.count i) = D.power i := by
  sorry

@[simp] theorem appendFactors_power_right (i : Fin E.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).power (Fin.natAdd D.count i) = E.power i := by
  sorry

@[simp] theorem appendFactors_decomposition_left (i : Fin D.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).decomposition (Fin.castAdd E.count i) = D.decomposition i := by
  sorry

@[simp] theorem appendFactors_decomposition_right (i : Fin E.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).decomposition (Fin.natAdd D.count i) = E.decomposition i := by
  sorry

@[simp] theorem appendFactors_factorIdeal_left (i : Fin D.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).factorIdeal (Fin.castAdd E.count i) = D.factorIdeal i := by
  sorry

@[simp] theorem appendFactors_factorIdeal_right (i : Fin E.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).factorIdeal (Fin.natAdd D.count i) = E.factorIdeal i := by
  sorry

@[simp] theorem appendFactors_factorCharacter_left (i : Fin D.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).factorCharacter (Fin.castAdd E.count i) = D.factorCharacter i := by
  sorry

@[simp] theorem appendFactors_factorCharacter_right (i : Fin E.count) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).factorCharacter (Fin.natAdd D.count i) = E.factorCharacter i := by
  sorry

theorem appendFactors_character :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).character = D.character * E.character := by
  sorry

theorem appendFactors_fullIdeal_val :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).fullIdeal.val = D.fullIdeal.val * E.fullIdeal.val := by
  sorry

theorem appendFactors_fullIdeal :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).fullIdeal = ExteriorIdealEuler.mul D.fullIdeal E.fullIdeal := by
  sorry

/-- No coprimality or distinction between the two lists is required. -/
theorem appendFactors_support_primes :
    primeSupport ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).support.val =
      primeSupport D.support.val ∪ primeSupport E.support.val := by
  sorry

/-- The displayed radical retains every original prime even if its
integer character exponent is zero or cancels another occurrence. -/
theorem appendFactors_support_val :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).support.val =
      commonRadical (D.support.val * E.support.val) (D.support.val * E.support.val) := by
  sorry

theorem appendFactors_support_coprime_iff (I : Ideal (𝓞 K)) :
    IsCoprime I ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).support.val ↔
      IsCoprime I D.support.val ∧ IsCoprime I E.support.val := by
  sorry

theorem appendFactors_fullMaskSupport_primes
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    primeSupport (((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).fullMaskSupport remaining).val =
      (primeSupport D.support.val ∪ primeSupport E.support.val) ∪
        primeSupport remaining.val := by
  sorry

theorem appendFactors_fullMaskSupport_coprime_iff
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    IsCoprime I (((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).fullMaskSupport remaining).val ↔
      (IsCoprime I D.support.val ∧ IsCoprime I E.support.val) ∧
        IsCoprime I remaining.val := by
  sorry

private theorem appended_mask_reorder (a b c d e : Bool) :
    ((a && (b && c)) && (d && e)) = ((((a && b) && d) && c) && e) := by
  sorry

/-- On the original complete-row gate the new mask is exactly the
old full mask, the appended factor mask and the full remaining-factor
mask. Normalizing the old remaining ideal deletes no effective zero. -/
theorem appendFactors_normalizedFullMask
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (F : A.Exterior) (I : Ideal (𝓞 K)) :
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).support.val)) &&
      decide (IsCoprime I (remainingMaskIdeal A remaining * exteriorMomentIdeal F).val)) =
    ((((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I D.support.val)) && decide (IsCoprime I remaining.val)) &&
      decide (IsCoprime I E.support.val)) && decide (IsCoprime I F.val)) := by
  sorry

theorem appendFactors_normalizedFullMask_primes
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (F : A.Exterior) :
    primeSupport (((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).fullMaskSupport
        (remainingMaskIdeal A remaining * exteriorMomentIdeal F)).val =
      (primeSupport D.support.val ∪ primeSupport E.support.val) ∪
        ((primeSupport remaining.val \ primeSupport A.cS) ∪ primeSupport F.val) := by
  sorry

namespace SupportAtoms

variable {D E} {old unit nonunit : A.Exterior}
variable {remaining : HeckeGeneral.Analysis.NonzeroIdeal K}

/-- The same original support dictionary, enlarged by an actual
remaining factor. Every listed element and its generator stays fixed. -/
def withRemainingFactor (W : D.SupportAtoms old unit nonunit remaining) (F : A.Exterior) :
    D.SupportAtoms (ExteriorIdealEuler.mul old F) unit nonunit
      (remaining * exteriorMomentIdeal F) where
  ideal := W.ideal
  generates := W.generates
  oldPower := W.oldPower
  unitPower := W.unitPower
  nonunitPower := W.nonunitPower
  factor_divides i := by
    change (W.ideal i).val ∣
      (old.val * F.val) ^ W.oldPower i * unit.val ^ W.unitPower i *
        nonunit.val ^ W.nonunitPower i
    exact (W.factor_divides i).trans
      (mul_dvd_mul (mul_dvd_mul
        (pow_dvd_pow_of_dvd (dvd_mul_right old.val F.val) (W.oldPower i))
        (dvd_refl _)) (dvd_refl _))
  remaining_divides := by
    change remaining.val * F.val ∣ (old.val * F.val) * unit.val * nonunit.val
    have hd := mul_dvd_mul W.remaining_divides (dvd_refl F.val)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hd

/-- Concatenation of the individual proved generator dictionaries. -/
def appendFactors
    (W : D.SupportAtoms old unit nonunit remaining)
    (V : E.SupportAtoms old unit nonunit remaining) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) E).SupportAtoms old unit nonunit remaining where
  ideal := Fin.append W.ideal V.ideal
  generates i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left, OriginalMovingFactors.appendFactors_element_left]
        using W.generates j
    · simpa only [Fin.append_right, OriginalMovingFactors.appendFactors_element_right]
        using V.generates j
  oldPower := Fin.append W.oldPower V.oldPower
  unitPower := Fin.append W.unitPower V.unitPower
  nonunitPower := Fin.append W.nonunitPower V.nonunitPower
  factor_divides i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using W.factor_divides j
    · simpa only [Fin.append_right] using V.factor_divides j
  remaining_divides := W.remaining_divides

end SupportAtoms

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual second active singleton is appended, never substituted
for the original list. Its exponent is the original exponent one. -/
def appendSecondFactor (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    OriginalMovingFactors A P Rchar :=
  (HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) (secondOriginalMovingFactors P Rchar C p m n pattern)

@[simp] theorem appendSecondFactor_count
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor D) C p m n pattern).count = D.count + 1 := rfl

theorem appendSecondFactor_character
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor D) C p m n pattern).character =
      D.character * (secondOriginalMovingFactors P Rchar C p m n pattern).character := by
  sorry

theorem appendSecondFactor_support_primes
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    primeSupport ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor D) C p m n pattern).support.val =
      primeSupport D.support.val ∪
        primeSupport (secondOriginalMovingFactors P Rchar C p m n pattern).support.val := by
  sorry

/-- Both old and new generator dictionaries are constructed from
their actual elements. The normalization of the original remaining
ideal is exact behind the complete-row mask, and the sixth root stays
in the new remaining ideal with its full multiplicity. -/
def appendSecondFullDeletionSupportAtoms
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor D) C p m n (actualNonunitPattern C p m n h)).SupportAtoms
      (ExteriorIdealEuler.mul (D.effectiveFullSupport remaining) (secondSixthRootIdeal p m n))
      (unitFrequencyRadical C p m n h) (nonunitFrequencyRadical C p m n h)
      (remainingMaskIdeal A remaining * secondSixthRootNonzeroIdeal p m n) :=
  (HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.SupportAtoms.appendFactors ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.SupportAtoms.withRemainingFactor (D.effectiveSupportAtoms remaining
      (unitFrequencyRadical C p m n h) (nonunitFrequencyRadical C p m n h)))
        (secondSixthRootIdeal p m n)))
    (secondOriginalMovingSupportAtoms P Rchar C p m n hm hn h hne
      (D.effectiveFullSupport remaining) (remainingMaskIdeal A remaining)
      (D.remainingMaskIdeal_dvd_effectiveFullSupport remaining))

/-- This quantitative support bound has no support or divisor input:
the old cost is its literal effective full-support logarithm. -/
theorem appendSecondFullDeletion_norm_window
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    idealNorm K
        (((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor D) C p m n (actualNonunitPattern C p m n h)).fullMaskSupport
          (remainingMaskIdeal A remaining * secondSixthRootNonzeroIdeal p m n)) ≤
      Z ^ (idealLogLength Z (D.effectiveFullSupport remaining).val +
        idealLogLength Z (secondSixthRootIdeal p m n).val +
        idealLogLength Z (unitFrequencyRadical C p m n h).val +
        idealLogLength Z (nonunitFrequencyRadical C p m n h).val) := by
  sorry

end OriginalMovingFactors

namespace ActualSecondCorrelationRows

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι)

/-- The actual original live correlation proves every local premise.
The fixed pattern changes only the support certificate, not the list. -/
def appendedNonunitClassSupportAtoms
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (C : A.GeneralArithmeticContext σ η hS)
    (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
    (pattern : ι → Bool) (h : S.NonunitClass C pattern) :
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor oldMoving) C S.primes S.leftMultiplicity S.rightMultiplicity pattern).SupportAtoms
      (ExteriorIdealEuler.mul (oldMoving.effectiveFullSupport remaining)
        (secondSixthRootIdeal S.primes S.leftMultiplicity S.rightMultiplicity))
      (unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val))
      (nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val))
      (remainingMaskIdeal A remaining *
        secondSixthRootNonzeroIdeal S.primes S.leftMultiplicity S.rightMultiplicity) := by
  have W := (HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFullDeletionSupportAtoms oldMoving) remaining C S.primes
    S.leftMultiplicity S.rightMultiplicity hm hn (S.frequency h.val.val)
    (S.live_local_correlation_nonzero C h.val)
  rw [h.property] at W
  exact W

end ActualSecondCorrelationRows

namespace CanonicalOriginalChildData

variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ)
variable (oldMoving newMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
  SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

/-- The new complete-row character keeps the original moving product
separate from the genuinely appended factor and the complete residual row. -/
theorem appended_rowCharacter (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (data parent ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors oldMoving) newMoving) correction hcorr sector remaining budget
      inverse left right geometry index).rowCharacter u =
      (correction * oldMoving.character * newMoving.character) *
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P Rchar (sector u) u := by
  sorry

/-- This is the literal mask of the same canonical child, with no
new mask equality supplied by its caller. -/
theorem appended_commonMask (F : A.Exterior)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    (data parent ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors oldMoving) newMoving) correction hcorr sector
      (remainingMaskIdeal A remaining * exteriorMomentIdeal F) budget
      inverse left right geometry index).commonMask u I =
    ((((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I oldMoving.support.val)) && decide (IsCoprime I remaining.val)) &&
      decide (IsCoprime I newMoving.support.val)) && decide (IsCoprime I F.val)) := by
  sorry

end CanonicalOriginalChildData

private theorem appendedFactors_width_shift
    (Z a₀ q wo krow g r : ℝ) (I J T V : Ideal (𝓞 K)) :
    secondCommonChildWidth Z a₀ (q + r) wo krow g I J T V =
      secondCommonChildWidth Z a₀ q wo krow g I J T V + r := by
  sorry

section ActualPatternWindows

open MeasureTheory

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

/-- The same physical frequency bound now pays the full appended
list. The sole old-support window concerns its original effective
ideal; all factor and remaining divisibilities are proved internally. -/
theorem actualRows_appended_pattern_fullDeletion_joint_window
    (hclass : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.NonunitLabelStable chart))
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) ∅ X hX label
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K
          (((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor oldMoving) C b.primes b.leftMultiplicity b.rightMultiplicity pattern).fullMaskSupport
            (remainingMaskIdeal A remaining *
              secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  sorry

/-- Every actual original live row enters this same child. The old
moving list, original finite correction, all tests and selected slots
are preserved; only the genuine second factor and root are appended. -/
theorem canonicalOriginalChild_allowed_of_appended_pattern
    (hclass : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.NonunitLabelStable chart))
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K) (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
      SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (inverseTest leftTest rightTest : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) ∅ X hX label
    (CanonicalOriginalChildData.data parent
      ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor oldMoving) C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
      correction hcorr sector
      (remainingMaskIdeal A remaining *
        secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
      (Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent))
      inverseTest leftTest rightTest geometry index).allowedRow
        ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal := by
  sorry

end SecondBlockProfileChart
end ActualPatternWindows

end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Literal residue calibration after appending the new moving factor

The source keeps every original moving character inside its actual Euler
coefficient.  The child appends the new active factor to the original
list and retains the full sixth root in its remaining deletion.  The
effective old support is used only through its proved complete-row mask
identity.  In particular no unramifiedness of the original moving or
background characters is assumed, and no character is added to theta.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalAppendedPhaseCalibration

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

/-- The entire old moving product remains in each original coefficient.
The finite-ray factor is the original trivial character. -/
def sourceCharacters (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k where
  plain := parent.plainBackground * correction * oldMoving.character
  slot i := parent.slotCoefficient (index i) * correction * oldMoving.character
  plainTwist := 1
  slotTwist _ := 1
  mask := originalCoprimeMask (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining))
  fixedRay := {1}
  plainTwist_mem := Finset.mem_singleton_self 1
  slotTwist_mem _ := Finset.mem_singleton_self 1

@[simp] theorem sourceCharacters_restrictSlots
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) (keep : Finset (Fin k)) :
    (sourceCharacters P R parent oldMoving correction remaining index).restrictSlots keep =
      sourceCharacters P R parent oldMoving correction remaining
        (fun i => index (SlotRestriction.index keep i)) := rfl

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual child uses the concatenated moving list and the full
new remaining sixth root.  All its raw fields are constructed here. -/
def childData (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (hcorr : correction ∈ parent.theta)
    (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
    (inverse left right : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) : MomentData K ω ψ :=
  CanonicalOriginalChildData.data parent
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor oldMoving) C primes m n pattern)
    correction (Or.inr hcorr) (fun _ => ν)
    (remainingMaskIdeal A remaining * exteriorMomentIdeal (secondSixthRootIdeal primes m n))
    budget inverse left right geometry index

variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (primes : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

private theorem common_mask_reorder (a b c d : Bool) :
    (((a && b) && c) && d) = ((a && c) && (b && d)) := by
  sorry

/-- The old support is collapsed only behind the same complete-row
gate.  This is an identity of the actual child masks, including zeros. -/
theorem childData_mask_eq (u J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    maskValue (childData P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index) u J.val =
    maskValue (CanonicalOriginalPhaseCalibration.childData P R parent correction hcorr
      C primes m n pattern ν (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining))
      budget inverse left right geometry index) u J.val := by
  sorry

/-- The original moving character is multiplied into the unchanged
source background; only the genuinely new active and row characters
are separated by the original residue dictionary. -/
theorem childData_rowCharacter (u : HeckeGeneral.Analysis.NonzeroIdeal K) (χ : HeckeCharacter K) :
    χ * (childData P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index).rowCharacter u =
    (χ * oldMoving.character) *
      (CanonicalOriginalPhaseCalibration.childData P R parent correction hcorr C primes m n
        pattern ν (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)) budget
        inverse left right geometry index).rowCharacter u := by
  sorry

variable {Ih : A.Exterior} {h g : A.R} {factor : ℝ}

theorem childData_row_coefficient
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) (χ : HeckeCharacter K) (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    heckeIdealCoefficient K
        (χ * (childData P R parent oldMoving correction hcorr C primes m n pattern ν
          remaining budget inverse left right geometry index).rowCharacter row.momentIdeal) J *
      maskValue (childData P R parent oldMoving correction hcorr C primes m n pattern ν
        remaining budget inverse left right geometry index) row.momentIdeal J.val =
      heckeIdealCoefficient K (χ * correction * oldMoving.character) J *
        originalCoprimeMask (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)) J.val *
        actualIdealResidue (A := A) (σ := σ) J.val g *
        actualIdealResidue (A := A) (σ := σ) J.val row.element := by
  sorry

/-- Single-ideal and single-prime identities for the same appended
child, with its literal original background and finite slot characters. -/
def calibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C primes m n pattern ν remaining budget
        inverse left right geometry index) rfl row.momentIdeal g row.element where
  fixedRay_mem_theta θ hθ := by
    have he : θ = 1 := Finset.mem_singleton.mp hθ
    subst θ
    exact hone
  plain J := by
    have he := childData_row_coefficient P R parent oldMoving correction hcorr C primes m n
      pattern ν remaining budget inverse left right geometry index hroot hemb
      row hfactor hsector parent.plainBackground J
    simpa only [sourceCharacters, sourcePlainCoefficient, coefficient_one, mul_one] using he
  slot i p := by
    let d := childData P R parent oldMoving correction hcorr C primes m n pattern ν
      remaining budget inverse left right geometry index
    have he := childData_row_coefficient P R parent oldMoving correction hcorr C primes m n
      pattern ν remaining budget inverse left right geometry index hroot hemb
      row hfactor hsector (parent.slotCoefficient (index i)) (primeIdeal p)
    simp only [coefficient_prime] at he
    change primeCoefficient K (parent.slotCoefficient (index i) * d.rowCharacter row.momentIdeal) p *
        maskValue d row.momentIdeal p.asIdeal =
      primeCoefficient K (parent.slotCoefficient (index i) * correction * oldMoving.character) p *
          (originalCoprimeMask (exteriorMomentIdeal (oldMoving.effectiveFullSupport remaining)))
            p.asIdeal *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal g *
          actualIdealResidue (A := A) (σ := σ) p.asIdeal row.element at he
    change primeCoefficient K (d.rowCharacter row.momentIdeal * parent.slotCoefficient (index i)) p *
      maskValue d row.momentIdeal p.asIdeal = _
    rw [mul_comm (d.rowCharacter row.momentIdeal) (parent.slotCoefficient (index i))]
    simpa only [sourceCharacters, sourcePrimeCoefficient, primeCoefficient_one,
      Fin.cast_refl, id_eq, mul_one] using he

def negativeCalibration
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : ActualChildRow Ih h g factor)
    (hfactor : g = secondSixthRootGenerator C primes m n ^ 6 *
      secondActiveFrequencyGenerator C primes m n pattern)
    (hsector : row.sector P = ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C primes m n pattern ν remaining budget
        inverse left right geometry index) rfl row.momentIdeal (-g) row.element where
  fixedRay_mem_theta := (calibration P R parent oldMoving correction hcorr C primes m n pattern
    ν remaining budget inverse left right geometry index hone hroot hemb
    row hfactor hsector).fixedRay_mem_theta
  plain J := by
    rw [residue_neg]
    exact (calibration P R parent oldMoving correction hcorr C primes m n pattern
      ν remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).plain J
  slot i p := by
    rw [residue_neg]
    exact (calibration P R parent oldMoving correction hcorr C primes m n pattern
      ν remaining budget inverse left right geometry index hone hroot hemb row hfactor hsector).slot i p

section ActualIndices

variable {H : Type*}

/-- Actual live rows supply their own factorization and sector. -/
def actualCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  calibration P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
    S.rightMultiplicity pattern ν remaining budget inverse left right geometry index
    hone hroot hemb (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

def actualNegativeCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R parent oldMoving correction remaining index).Calibration (σ := σ)
      (childData P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining budget inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  negativeCalibration P R parent oldMoving correction hcorr C S.primes S.leftMultiplicity
    S.rightMultiplicity pattern ν remaining budget inverse left right geometry index
    hone hroot hemb (S.extractedRow C q.val.val) (S.factor_nonunitClass C pattern q.val) q.property

/-- The same actual allocation acts on both the source dictionary and
the chosen child. No second removal choice is made in the calibration. -/
def actualAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R parent oldMoving correction remaining index).restrictSlots B.keep).Calibration
      (σ := σ) ((childData P R parent oldMoving correction hcorr C S.primes
        S.leftMultiplicity S.rightMultiplicity pattern ν remaining budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  (actualCalibration P R parent oldMoving correction hcorr C pattern ν remaining budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

def actualNegativeAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R parent oldMoving correction remaining index).restrictSlots B.keep).Calibration
      (σ := σ) ((childData P R parent oldMoving correction hcorr C S.primes
        S.leftMultiplicity S.rightMultiplicity pattern ν remaining budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  (actualNegativeCalibration P R parent oldMoving correction hcorr C pattern ν remaining budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

end ActualIndices

end HeckeSkeleton.Moments.EngineStepV2.CanonicalAppendedPhaseCalibration

end

/-!
# The support actually excluded by the literal child mask

At an original common prime, the active exponent and the complete sixth
root together have positive multiplicity.  This remains true when the
active exponent vanishes.  Consequently the actual child mask excludes
every prime of both original common ideals, for every Boolean pattern.

The old displayed factors and the original remaining ideal are also
retained.  Replacing the remaining ideal by its exterior radical is used
only through the exact complete-row mask identity.  These are consequences
of the nonzero literal mask; no live-row, nonempty-row, finite-support, or
whole-polynomial hypothesis is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralMaskSupport

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The active remainder and the full sixth root cover an original
prime even for an arbitrary, possibly unrealized, nonunit pattern. -/
theorem active_add_root_positive (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (pattern : Bool) :
    1 ≤ (min m n % 6 + if pattern then 1 else 0) + min m n / 6 := by
  sorry

/-- This stronger product divisibility does not require the prime list
to be injective.  It therefore also supplies the support argument without
using any correlation or row condition. -/
theorem prime_product_dvd_active_root
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    (primePowerProduct p (fun _ => 1)).val ∣
      (secondActiveFrequencyIdeal p m n pattern).val *
        (secondSixthRootIdeal p m n).val := by
  sorry

/-- In the actual injective prime dictionary, the preceding product is
the radical of the two common ideals. -/
theorem common_radical_dvd_active_root
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    commonRadical (primePowerProduct p m).val (primePowerProduct p n).val ∣
      (secondActiveFrequencyIdeal p m n pattern).val *
        (secondSixthRootIdeal p m n).val := by
  sorry

theorem coprime_each_prime_of_active_root
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (I : Ideal (𝓞 K))
    (hactive : IsCoprime I (secondActiveFrequencyIdeal p m n pattern).val)
    (hroot : IsCoprime I (secondSixthRootIdeal p m n).val) (i : ι) :
    IsCoprime I (p i).val.asIdeal := by
  sorry

theorem coprime_common_of_active_root
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (I : Ideal (𝓞 K))
    (hactive : IsCoprime I (secondActiveFrequencyIdeal p m n pattern).val)
    (hroot : IsCoprime I (secondSixthRootIdeal p m n).val) :
    IsCoprime I (primePowerProduct p m).val ∧
      IsCoprime I (primePowerProduct p n).val := by
  sorry

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The primitive coprimalities recovered from one actual nonzero mask.
This record is an output of `childData_mask_nonzero`, not an input to the
construction of the child or its finite support. -/
structure MaskConsequences (oldMoving : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool)
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K) : Prop where
  fixed : IsCoprime I.val A.cS
  row : IsCoprime I.val u.val
  old_support : IsCoprime I.val oldMoving.support.val
  old_remaining : IsCoprime I.val remaining.val
  active : IsCoprime I.val (secondActiveFrequencyIdeal p m n pattern).val
  root : IsCoprime I.val (secondSixthRootIdeal p m n).val

namespace MaskConsequences

variable {oldMoving : OriginalMovingFactors A P R}
variable {remaining : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {p : ι → ExteriorPrime A} {m n : ι → ℕ} {pattern : ι → Bool}
variable {u I : HeckeGeneral.Analysis.NonzeroIdeal K}
variable (H : MaskConsequences oldMoving remaining p m n pattern u I)
include H

theorem old_full_support :
    IsCoprime I.val (oldMoving.fullMaskSupport remaining).val := by
  sorry

theorem old_full_support_prime (q : Ideal (𝓞 K))
    (hq : q ∈ primeSupport (oldMoving.fullMaskSupport remaining).val) :
    IsCoprime I.val q := by
  sorry

/-- In particular every first or pool singleton previously appended to
the moving list remains excluded, including exponent-zero occurrences. -/
theorem old_factor (i : Fin oldMoving.count) :
    IsCoprime I.val (oldMoving.factorIdeal i).val := by
  sorry

theorem old_factor_prime (i : Fin oldMoving.count) (q : Ideal (𝓞 K))
    (hq : q ∈ primeSupport (oldMoving.factorIdeal i).val) :
    IsCoprime I.val q := by
  sorry

theorem second_prime (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (i : ι) :
    IsCoprime I.val (p i).val.asIdeal := by
  sorry

theorem second_common (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    IsCoprime I.val (primePowerProduct p m).val ∧
      IsCoprime I.val (primePowerProduct p n).val := by
  sorry

theorem second_left_prime (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (q : Ideal (𝓞 K)) (hq : q ∈ primeSupport (primePowerProduct p m).val) :
    IsCoprime I.val q := by
  sorry

theorem second_right_prime (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (q : Ideal (𝓞 K)) (hq : q ∈ primeSupport (primePowerProduct p n).val) :
    IsCoprime I.val q := by
  sorry

end MaskConsequences

variable {ω ψ : HeckeCharacter K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (m n : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

/-- Recover the original coprimality conditions from the same child
used by the actual appended phase calibration. -/
theorem childData_mask_nonzero (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue
      (CanonicalAppendedPhaseCalibration.childData P R parent oldMoving correction hcorr
        C p m n pattern ν remaining budget inverse left right geometry index) u I.val ≠ 0) :
    MaskConsequences oldMoving remaining p m n pattern u I := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralMaskSupport

end

/-!
# Literal source characters and the actual appended child calibration

The first divisor, pool reciprocity and empty-mask unit elements are
inserted as three genuine moving singletons.  An additional deletion
ideal retains the passive first common primes.  Its full multiplicity is
kept in the remaining ideal of the same child.

The literal source mask and the child's exterior-radical source mask
agree on ideals coprime to the original fixed S.  Outside that gate the
actual residue is zero.  Transporting the two single-atom identities by
these facts gives the actual arithmetic calibration, without assuming
equality of entire source records or of whole polynomials.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPhaseCalibration

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

/-- Only the original three generated elements occur here.  In
particular the first element is not assumed to contain passive primes. -/
structure FixedPhases (A : SArithmeticData K) where
  firstIdeal : A.Exterior
  poolIdeal : A.Exterior
  unitIdeal : A.Exterior
  firstElement : A.R
  poolElement : A.R
  unitElement : A.R
  first_generates : A.Generates firstIdeal firstElement
  pool_generates : A.Generates poolIdeal poolElement
  unit_generates : A.Generates unitIdeal unitElement

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

namespace FixedPhases

variable (F : FixedPhases A)

def firstMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ⟨F.firstElement, F.first_generates.1⟩ 1

def poolMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ⟨F.poolElement, F.pool_generates.1⟩ 1

def unitMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton ⟨F.unitElement, F.unit_generates.1⟩ 1

/-- The list is appended in exactly the order of the literal atom
operations.  No exponent is combined or cancelled. -/
def moving (D : OriginalMovingFactors A P R) : OriginalMovingFactors A P R :=
  (HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendFactors D) (F.firstMoving P R))) (F.poolMoving P R)))
    (F.unitMoving P R)

theorem moving_character (D : OriginalMovingFactors A P R) :
    (F.moving P R D).character =
      ((D.character * (F.firstMoving P R).character) * (F.poolMoving P R).character) *
        (F.unitMoving P R).character := by
  sorry

private theorem singleton_support_coprime
    (J : A.Exterior) (a : A.R) (ha : A.Generates J a) (I : Ideal (𝓞 K)) :
    IsCoprime I (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support.val ↔
      IsCoprime I J.val := by
  sorry

theorem moving_support_coprime (D : OriginalMovingFactors A P R) (I : Ideal (𝓞 K)) :
    IsCoprime I (F.moving P R D).support.val ↔
      ((IsCoprime I D.support.val ∧ IsCoprime I F.firstIdeal.val) ∧
        IsCoprime I F.poolIdeal.val) ∧ IsCoprime I F.unitIdeal.val := by
  sorry

/-- The extra mask is a separate deletion, independent of whether a
prime appears in one of the fixed residue phases. -/
def applyCharacters {k : ℕ} (T : FixedChildCharacters K k)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) : FixedChildCharacters K k :=
  ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.movingSingleton P R ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.movingSingleton P R ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.movingSingleton P R T) F.firstIdeal F.firstElement F.first_generates)) F.poolIdeal F.poolElement F.pool_generates)) F.unitIdeal F.unitElement F.unit_generates)) extra)

@[simp] theorem applyCharacters_restrictSlots {k : ℕ} (T : FixedChildCharacters K k)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) (keep : Finset (Fin k)) :
    (F.applyCharacters P R T extra).restrictSlots keep =
      F.applyCharacters P R (T.restrictSlots keep) extra := rfl

end FixedPhases

private theorem effective_support_coprime
    (D : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (I : Ideal (𝓞 K)) (hI : IsCoprime I A.cS) :
    IsCoprime I (D.effectiveFullSupport remaining).val ↔
      IsCoprime I D.support.val ∧ IsCoprime I remaining.val := by
  sorry

private theorem mask_indicator_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ℂ) else 0) * (if q then 1 else 0) =
      if p ∧ q then 1 else 0 := by
  sorry

section Source

variable {ω ψ : HeckeCharacter K}

/-- The source is formed from the actual original character and raw
mask, before the three moving operations and extra common deletion. -/
def sourceCharacters (F : FixedPhases A) (parent : MomentData K ω ψ)
    (D : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k :=
  F.applyCharacters P R
    (CanonicalOriginalPhaseCalibration.sourceCharacters parent
      (correction * D.character) (exteriorMomentIdeal D.support * remaining) index) extra

variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (D : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
variable (index : Fin k → Fin parent.geometry.slotCount)

@[simp] theorem sourceCharacters_restrictSlots (keep : Finset (Fin k)) :
    (sourceCharacters P R F parent D correction remaining extra index).restrictSlots keep =
      sourceCharacters P R F parent D correction remaining extra
        (fun i => index (SlotRestriction.index keep i)) := rfl

theorem sourceCharacters_plain :
    (sourceCharacters P R F parent D correction remaining extra index).plain =
      (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
        correction (remaining * extra) index).plain := by
  sorry

theorem sourceCharacters_slot (i : Fin k) :
    (sourceCharacters P R F parent D correction remaining extra index).slot i =
      (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
        correction (remaining * extra) index).slot i := by
  sorry

/-- This equality uses exactly the original fixed-S gate.  It is not
asserted for arbitrary ideals outside that gate. -/
theorem sourceCharacters_mask (I : Ideal (𝓞 K)) (hI : IsCoprime I A.cS) :
    (sourceCharacters P R F parent D correction remaining extra index).mask I =
      (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
        correction (remaining * extra) index).mask I := by
  sorry

theorem sourceCharacters_plain_coefficient
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : IsCoprime I.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent D correction remaining extra index).plain
        (sourceCharacters P R F parent D correction remaining extra index).plainTwist
        (sourceCharacters P R F parent D correction remaining extra index).mask I =
      sourcePlainCoefficient
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).plain
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).plainTwist
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).mask I := by
  sorry

theorem sourceCharacters_prime_coefficient (i : Fin k) (p : HeightOneSpectrum (𝓞 K))
    (hp : IsCoprime p.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent D correction remaining extra index).slot i)
        ((sourceCharacters P R F parent D correction remaining extra index).slotTwist i)
        (sourceCharacters P R F parent D correction remaining extra index).mask p =
      sourcePrimeCoefficient
        ((CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).slot i)
        ((CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).slotTwist i)
        (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
          correction (remaining * extra) index).mask p := by
  sorry

variable {σ : K →+* ℂ}

private def calibrationOfCanonical (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (original : (CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R D)
      correction (remaining * extra) index).Calibration (σ := σ) d count u g h') :
    (sourceCharacters P R F parent D correction remaining extra index).Calibration
      (σ := σ) d count u g h' where
  fixedRay_mem_theta := original.fixedRay_mem_theta
  plain I := by
    rw [original.plain I]
    by_cases hI : IsCoprime I.val A.cS
    · rw [sourceCharacters_plain_coefficient P R F parent D correction remaining extra index I hI]
    · have hzero : actualIdealResidue (A := A) (σ := σ) I.val g = 0 := by
        exact dif_neg (fun h => hI h.2)
      simp only [hzero, mul_zero, zero_mul]
  slot i p := by
    rw [original.slot i p]
    by_cases hp : IsCoprime p.asIdeal A.cS
    · rw [sourceCharacters_prime_coefficient P R F parent D correction remaining extra index
        (Fin.cast count i) p hp]
    · have hzero : actualIdealResidue (A := A) (σ := σ) p.asIdeal g = 0 := by
        exact dif_neg (fun h => hp h.2)
      simp only [hzero, mul_zero, zero_mul]

end Source

section ActualIndices

variable {ω ψ : HeckeCharacter K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (D : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable (inverse left right : IdealTest K) (geometry : SlotGeometry K)
variable (index : Fin geometry.slotCount → Fin parent.geometry.slotCount)

/-- The original pattern-sector row supplies its genuine generator
factorization. Only the already proved single-atom identities are
transported from the exterior-radical source to the literal source. -/
def actualCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R F parent D correction remaining extra index).Calibration (σ := σ)
      (CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  calibrationOfCanonical P R F parent D correction remaining extra index _ rfl _ _ _
    (CanonicalAppendedPhaseCalibration.actualCalibration P R parent (F.moving P R D)
      correction hcorr C pattern ν (remaining * extra) budget inverse left right geometry index
      S hone hroot hemb q)

def actualNegativeCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    (sourceCharacters P R F parent D correction remaining extra index).Calibration (σ := σ)
      (CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  calibrationOfCanonical P R F parent D correction remaining extra index _ rfl _ _ _
    (CanonicalAppendedPhaseCalibration.actualNegativeCalibration P R parent (F.moving P R D)
      correction hcorr C pattern ν (remaining * extra) budget inverse left right geometry index
      S hone hroot hemb q)

/-- The chosen allocation is unchanged. Both the literal dictionary
and the original child use its same retained-slot map. -/
def actualAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R F parent D correction remaining extra index).restrictSlots B.keep).Calibration
      (σ := σ)
      ((CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (S.factor C q.val.val.val)
      (S.extractedRow C q.val.val).element :=
  (actualCalibration P R F parent D correction hcorr C pattern ν remaining extra budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

def actualNegativeAllocatedCalibration (S : ActualSecondCorrelationRows A σ H ι)
    (B : ActualColumnAllocation K geometry.slotCount)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (q : PatternSector P S C pattern ν) :
    ((sourceCharacters P R F parent D correction remaining extra index).restrictSlots B.keep).Calibration
      (σ := σ)
      ((CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R D) correction hcorr
        C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν (remaining * extra) budget
        inverse left right geometry index).restrictSlots B.keep) rfl
      (S.extractedRow C q.val.val).momentIdeal (-(S.factor C q.val.val.val))
      (S.extractedRow C q.val.val).element :=
  (actualNegativeCalibration P R F parent D correction hcorr C pattern ν remaining extra budget
    inverse left right geometry index S hone hroot hemb q).restricted B.keep

end ActualIndices

section OriginalSource

variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (F : FixedPhases A)

/-- The actual original recipe's raw product mask is definitionally
the starting mask used above. All three singleton operations remain
the literal operations on that source. -/
theorem apply_literalSourceCharacters (ξ : X)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    F.applyCharacters P R (Q.literalSourceCharacters ξ) extra =
      sourceCharacters P R F (data ξ) Q.moving Q.correction Q.remaining extra id := rfl

theorem apply_literalSourceCharacters_restricted (ξ : X)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (keep : Finset (Fin (data ξ).geometry.slotCount)) :
    F.applyCharacters P R ((Q.literalSourceCharacters ξ).restrictSlots keep) extra =
      sourceCharacters P R F (data ξ) Q.moving Q.correction Q.remaining extra
        (SlotRestriction.index keep) := rfl

/-- The existing recipe permits the original correction to be one;
the original theta identity supplies that case internally. -/
theorem original_correction_mem (ξ : X)
    (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta) :
    Q.correction ∈ (data ξ).theta := by
  sorry

end OriginalSource

section ActualAtoms

variable {σ : K →+* ℂ} {k : ℕ}
variable (F : FixedPhases A) (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- All norm powers, the extracted scalar and the Gauss normalizers
leave the characters alone. The three actual moving operations and
the independent full common deletion are exactly those calibrated
above; the original first extraction supplies their slot map. -/
theorem secondInput_characters (power : A.Exterior) (δ₁ δ₂ : ℝ)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((d.secondInput (σ := σ) b P R power F.firstIdeal F.poolIdeal F.unitIdeal
      F.firstElement F.poolElement F.unitElement F.first_generates F.pool_generates
      F.unit_generates δ₁ δ₂).deleteMask extra).characters =
      F.applyCharacters P R (d.characters.restrictSlots b.keep) extra := rfl

end ActualAtoms

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPhaseCalibration

end

/-!
# Actual Fourier profiles and parameters of one allocated literal source

The Fourier tests use the pre-allocation plain scales.  The two numeric
plain parameters are logarithms of the actual quotient scales, while
the prime geometry uses the same allocation's retained-slot map.  The
original parent time was already frozen by `ProfileData`, so the new
height is zero.  No arithmetic indicator is inserted into a smooth
profile and no nonnegativity of a quotient logarithm is presumed.

The final data constructor calls the existing appended-child constructor
with these profiles and then restricts that same child by the actual
allocation.  Its arithmetic dictionary is the literal phase calibration
already proved from the original three fixed generated elements.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralAllocatedData

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

section Parameters

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (B : ActualColumnAllocation K k) (rectangle : Bool) (m q κ : ℝ)

/-- The raw quotient logarithms may be negative.  The actual clipping
step subsequently handles that case with its recorded clipping cost. -/
def parameters : RealParameters where
  m := m
  r := 0
  z := ∑ i : Fin B.keep.card, d.length (SlotRestriction.index B.keep i)
  q := q
  n₁ := Real.logb d.base (d.scale₁ rectangle / idealNorm K (B.plainDivisor 0))
  n₂ := Real.logb d.base
    (d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0)))
  κ := κ

theorem left_scale :
    d.base ^ (parameters d B rectangle m q κ).n₁ =
      d.scale₁ rectangle / idealNorm K (B.plainDivisor 0) := by
  sorry

theorem right_scale :
    d.base ^ (parameters d B rectangle m q κ).n₂ =
      d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0)) := by
  sorry

@[simp] theorem slot_sum :
    (parameters d B rectangle m q κ).z =
      ∑ i : Fin B.keep.card, d.length (SlotRestriction.index B.keep i) := rfl

theorem slot_sum_nonneg : 0 ≤ (parameters d B rectangle m q κ).z := by
  sorry

@[simp] theorem parameters_width :
    (parameters d B rectangle m q κ).m + (parameters d B rectangle m q κ).q = m + q := rfl

@[simp] theorem parameters_kappa : (parameters d B rectangle m q κ).κ = κ := rfl

end Parameters

/-- The original time is frozen in the literal profile table. -/
def height (_ξ : WithLp 2 (ℝ × ℝ)) : ℝ := 0

section Profiles

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (firstSign : ℝ) (negative : Bool)

def preGeometry (ξ : WithLp 2 (ℝ × ℝ)) : SlotGeometry K where
  slotCount := k
  slots i := W.fourierSlot i firstSign negative ξ

def geometry (ξ : WithLp 2 (ℝ × ℝ)) : SlotGeometry K :=
  (preGeometry W firstSign negative ξ).restrictSlots B.keep

@[simp] theorem preGeometry_count (ξ : WithLp 2 (ℝ × ℝ)) :
    (preGeometry W firstSign negative ξ).slotCount = k := rfl

@[simp] theorem geometry_count (ξ : WithLp 2 (ℝ × ℝ)) :
    (geometry W B firstSign negative ξ).slotCount = B.keep.card := rfl

theorem preGeometry_length (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin k) :
    ((preGeometry W firstSign negative ξ).slots i).length = d.length i := by
  sorry

theorem geometry_length (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) :
    ((geometry W B firstSign negative ξ).slots i).length =
      d.length (SlotRestriction.index B.keep i) := by
  sorry

theorem geometry_totalLength (ξ : WithLp 2 (ℝ × ℝ)) :
    (geometry W B firstSign negative ξ).totalLength =
      ∑ i : Fin B.keep.card, d.length (SlotRestriction.index B.keep i) := by
  sorry

/-- The chosen allocation uses the original mesh, through its literal
retained-slot embedding. No coarser mesh is introduced. -/
theorem geometry_fitsMesh (mesh : ℝ)
    (hmesh : ∀ i ∈ B.keep, d.length i ≤ mesh) (ξ : WithLp 2 (ℝ × ℝ)) :
    (geometry W B firstSign negative ξ).fitsMesh mesh := by
  sorry

theorem geometry_slot_sum (rectangle : Bool) (m q κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (parameters d B rectangle m q κ).z =
      (geometry W B firstSign negative ξ).totalLength := by
  sorry

/-- The phase contains the original product `B₁ * I`; the Fourier
multiplier has not been incorrectly rescaled to the quotient alone. -/
theorem left_profile (rectangle : Bool) (m q κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    d.rectangleLeftWeight rectangle (B.plainDivisor 0 * I) *
        jointPhase ξ (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0 * I))) =
      (W.fourierLeft rectangle firstSign negative ξ).profile u (height ξ)
        (idealNorm K I / d.base ^ (parameters d B rectangle m q κ).n₁) := by
  sorry

theorem right_profile (rectangle : Bool) (m q κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    d.rightWeight rectangle (B.plainDivisor (Fin.succ 0) * I) *
        jointPhase ξ (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0) * I))) =
      (W.fourierRight rectangle firstSign negative ξ).profile u (height ξ)
        (idealNorm K I / d.base ^ (parameters d B rectangle m q κ).n₂) := by
  sorry

theorem slot_profile (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    d.slotWeight (SlotRestriction.index B.keep i) p *
        jointPhase ξ (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.prime firstSign (SlotRestriction.index B.keep i) p)) =
      ((geometry W B firstSign negative ξ).slots i).profile (height ξ)
        ((Ideal.absNorm p.asIdeal : ℝ) /
          d.base ^ ((geometry W B firstSign negative ξ).slots i).length) := by
  sorry

end Profiles

section ArithmeticData

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

/-- A literal invocation of the existing child constructor, using
computed Fourier tests, then the original allocation's restriction.
The input is raw parent arithmetic, not a selected calibrated child. -/
def data (ξ : WithLp 2 (ℝ × ℝ)) : MomentData K ω ψ :=
  (CanonicalAppendedPhaseCalibration.childData P R parent (F.moving P R oldMoving)
    correction hcorr C p leftMultiplicity rightMultiplicity pattern ν (remaining * extra)
    (d.base ^ (m + q)) inverse (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index).restrictSlots B.keep

@[simp] theorem data_count (ξ : WithLp 2 (ℝ × ℝ)) :
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).geometry.slotCount =
        B.keep.card := rfl

theorem data_lengths (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) :
    ((data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).geometry.slots i).length =
        d.length (SlotRestriction.index B.keep i) := by
  sorry

/-- The literal frozen profiles themselves construct the norm recipe
on every new allowed row; no row-independence field is requested. -/
def normProfiles : NormProfileRecipe
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative) where
  left ξ _ y := (W.fourierLeft rectangle firstSign negative ξ).profile 1 0 y
  right ξ _ y := (W.fourierRight rectangle firstSign negative ξ).profile 1 0 y
  left_eq ξ u _ time y := W.fourierLeft_frozen rectangle firstSign negative ξ u time y
  right_eq ξ u _ time y := W.fourierRight_frozen rectangle firstSign negative ξ u time y

variable {H : Type*}

/-- The same actual pattern-sector row and allocation provide the
arithmetic fields for the computed Fourier data. -/
def actualDictionary (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving correction
      remaining extra index).restrictSlots B.keep).Calibration (σ := σ)
      (data P R W B F parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
        negative ξ) rfl (S.extractedRow C row.val.val).momentIdeal (S.factor C row.val.val.val)
      (S.extractedRow C row.val.val).element :=
  CanonicalLiteralPhaseCalibration.actualAllocatedCalibration P R F parent oldMoving correction
    hcorr C pattern ν remaining extra (d.base ^ (m + q)) inverse
    (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index S B hone hroot hemb row

def actualNegativeDictionary (S : ActualSecondCorrelationRows A σ H ι)
    (hone : (1 : HeckeCharacter K) ∈ parent.theta)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((CanonicalLiteralPhaseCalibration.sourceCharacters P R F parent oldMoving correction
      remaining extra index).restrictSlots B.keep).Calibration (σ := σ)
      (data P R W B F parent oldMoving correction hcorr C S.primes S.leftMultiplicity
        S.rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
        negative ξ) rfl (S.extractedRow C row.val.val).momentIdeal (-(S.factor C row.val.val.val))
      (S.extractedRow C row.val.val).element :=
  CanonicalLiteralPhaseCalibration.actualNegativeAllocatedCalibration P R F parent oldMoving
    correction hcorr C pattern ν remaining extra (d.base ^ (m + q)) inverse
    (W.fourierLeft rectangle firstSign negative ξ)
    (W.fourierRight rectangle firstSign negative ξ) (preGeometry W firstSign negative ξ)
    index S B hone hroot hemb row

end ArithmeticData

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralAllocatedData

end

/-!
# Effective support of the actual allocated literal child

The original support table starts outside the fixed set S, and its two
actual common-ideal extractions add their prime supports.  The first
complete deletion is present in the remaining ideal.  At the second
extraction the active factor and the complete sixth root together remove
every common prime, including those with zero active exponent.

Consequently the nonzero mask of the child constructed in
`CanonicalLiteralAllocatedData` implies precisely the avoidance needed
by the original finite support table.  The three effective-support
conclusions below retain that same child, its smooth Fourier profiles,
the actual allocation and its occurrence indices.  No final support or
whole-mask implication is supplied as an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralAllocatedSupport

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralSupport CanonicalLiteralMaskSupport
open CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each first deleted prime divides the literal complete deletion,
independently of whether it occurs in an active reciprocity factor. -/
theorem dvd_literalDeletionIdeal (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (p : Ideal (𝓞 K)) (hp : p ∈ S) :
    p ∣ (literalDeletionIdeal S hS).val := by
  sorry

section PrimitiveAvoidance

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {oldMoving : OriginalMovingFactors A P R}
variable {remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K}
variable {p : ι → ExteriorPrime A} {l r : ι → ℕ} {pattern : ι → Bool}
variable {u I : HeckeGeneral.Analysis.NonzeroIdeal K}

/-- Only the original individual prime inclusions occur as inputs.
All coprimality statements are obtained from the actual child mask. -/
theorem avoids_of_maskConsequences
    (H : MaskConsequences oldMoving (remaining * extra) p l r pattern u I)
    (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ q ∈ firstSupport, q ∣ extra.val)
    (hsecond : secondSupport ⊆ primeSupport (primePowerProduct p l).val)
    (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i) :
    Avoids I.val ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport) := by
  sorry

end PrimitiveAvoidance

section ActualData

variable {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "child" => data P R W B F parent oldMoving correction hcorr C p
  leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
  rectangle firstSign negative

/-- Restricting the allocated slots does not alter the complete mask.
The output records the old moving factors, the entire first deletion,
and the complete new active/root factors. -/
theorem mask_consequences (ξ : WithLp 2 (ℝ × ℝ))
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue (child ξ) u I.val ≠ 0) :
    MaskConsequences (F.moving P R oldMoving) (remaining * extra) p
      leftMultiplicity rightMultiplicity pattern u I := by
  sorry

/-- The source may use its original finite support presentation, with
its prime-by-prime inclusion in the actual two deletions. -/
theorem mask_nonzero_avoids
    (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ v ∈ firstSupport, v ∣ extra.val)
    (hsecond : secondSupport ⊆ primeSupport (primePowerProduct p leftMultiplicity).val)
    (hl : ∀ i, 0 < leftMultiplicity i) (hr : ∀ i, 0 < rightMultiplicity i)
    (ξ : WithLp 2 (ℝ × ℝ)) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue (child ξ) u I.val ≠ 0) :
    Avoids I.val ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport) := by
  sorry

/-- All three support fields of the actual calibration follow from
the original atom support table and individual prime inclusions.
The profile functions themselves retain their original smooth values. -/
theorem effectiveSupports
    (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (hfirst : ∀ v ∈ firstSupport, v ∣ extra.val)
    (hsecond : secondSupport ⊆ primeSupport (primePowerProduct p leftMultiplicity).val)
    (hl : ∀ i, 0 < leftMultiplicity i) (hr : ∀ i, 0 < rightMultiplicity i)
    (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport))
    (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
    (hslots : B.slots = d.slots) (κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.base ^ (parameters d B rectangle m q κ).n₁) (height ξ) B.childPlain₁ ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.base ^ (parameters d B rectangle m q κ).n₂) (height ξ) B.childPlain₂ ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          (B.childSlots (Fin.cast
            (data_count P R W B F parent oldMoving correction hcorr C p
              leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
              rectangle firstSign negative ξ) i)) := by
  sorry

/-- Actual main/direct and pool tables delete their complete original
first support with `literalDeletionIdeal`; their second extraction uses
the displayed common support.  For those computed tables even the
individual prime-inclusion inputs of `effectiveSupports` are proved
internally. `hextra` is the literal recipe identity (normally `rfl`). -/
theorem effectiveSupports_of_original_deletions
    (firstSupport : Finset (Ideal (𝓞 K))) (hfirst : ∀ v ∈ firstSupport, Prime v)
    (hextra : extra = literalDeletionIdeal firstSupport hfirst)
    (hl : ∀ i, 0 < leftMultiplicity i) (hr : ∀ i, 0 < rightMultiplicity i)
    (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
      primeSupport (primePowerProduct p leftMultiplicity).val))
    (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
    (hslots : B.slots = d.slots) (κ : ℝ)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.base ^ (parameters d B rectangle m q κ).n₁) (height ξ) B.childPlain₁ ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.base ^ (parameters d B rectangle m q κ).n₂) (height ξ) B.childPlain₂ ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          (B.childSlots (Fin.cast
            (data_count P R W B F parent oldMoving correction hcorr C p
              leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
              rectangle firstSign negative ξ) i)) := by
  sorry

/-- The slot characters are the same original characters selected by
the actual occurrence embedding, including when no slot is retained. -/
theorem slot_in_theta (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin (child ξ).geometry.slotCount) :
    (child ξ).slotCoefficient i ∈ (child ξ).theta := by
  sorry

/-- A condition on the original background alone supplies the
principal-row implication.  The finite set theta is not assumed to be
a subgroup, and its membership is not enlarged for the child. -/
theorem principal_in_theta
    (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
      ¬ FiniteOrder parent.plainBackground)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hprincipal : (child ξ).plainBackground * (child ξ).rowCharacter u = 1) :
    (child ξ).rowCharacter u ∈ (child ξ).theta := by
  sorry

end ActualData

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralAllocatedSupport

end

/-!
# The original sector on the actual ordinary arithmetic rows

Moving the two common atoms into the row weight changes no arithmetic
row.  Deleting correlation-zero rows and then taking the ordinary rows
changes only their membership proofs.  The pattern and sector already
fixed by the original physical row label therefore give the literal
`PatternSector` dictionary on this same final row carrier.

The constructors below select no row and no child.  In particular they
do not need an ordinary-source witness or a normalized family in order
to choose the arithmetic data used by that family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (hpattern : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.NonunitLabelStable chart)) (hsector : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.SectorLabelStable chart) P)
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))

/-- Two successive restrictions retain the exact original arithmetic
extraction, even after its common scalar has been moved into the weight. -/
def originalReweightedPatternSector
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows M X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) :
    PatternSector P
      ((({ chart.actualRows M X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) C
      ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label) ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalSector chart) P M X hX label) := by
  let R₁ := { chart.actualRows M X hX label with weight := weight }
  let R₂ := R₁.restrictRows keep₁
  let h₁ : R₂.live := R₂.liveInclusion keep₂ h
  let h₀ : (chart.actualRows M X hX label).live := R₁.liveInclusion keep₁ h₁
  let hp := (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalPatternSector chart) P hpattern hsector M X hX label h₀
  exact ⟨⟨h, hp.val.property⟩, hp.property⟩

@[simp] theorem originalReweightedPatternSector_val_val
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ chart.actualRows M X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) :
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalReweightedPatternSector chart) P hpattern hsector M X hX label
      weight keep₁ keep₂ h).val.val = h := rfl

variable {kLeft kRight : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kLeft)
variable (rightAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kRight)
variable (exceptional : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)

/-- This is the carrier used by the actual common-atom mass dictionary
and the ordinary rectangle frames.  All four row updates are literal. -/
def originalSupportedPatternSector
    (h : ((((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms).restrictRows (fun q => (chart.actualRows M X hX label).correlation q ≠ 0)).restrictRows (fun q => ¬exceptional q)).live) :
    PatternSector P
      ((((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms).restrictRows (fun q => (chart.actualRows M X hX label).correlation q ≠ 0)).restrictRows (fun q => ¬exceptional q)) C
      ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label) ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalSector chart) P M X hX label) :=
  (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalReweightedPatternSector chart) P hpattern hsector M X hX label
    (fun q => (chart.actualRows M X hX label).weight q *
      leftAtoms.value q * star (rightAtoms.value q))
    (fun q => (chart.actualRows M X hX label).correlation q ≠ 0)
    (fun q => ¬exceptional q) h

@[simp] theorem originalSupportedPatternSector_val_val
    (h : ((((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms).restrictRows (fun q => (chart.actualRows M X hX label).correlation q ≠ 0)).restrictRows (fun q => ¬exceptional q)).live) :
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalSupportedPatternSector chart) P hpattern hsector M X hX label
      leftAtoms rightAtoms exceptional h).val.val = h := rfl

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The actual common row character before either rectangle is normalized

The character is computed from the original correction, the complete
moving list and the original residual sector. It is independent of the
two plain profiles, their comparison scales, the slot allocation and
both Fourier variables. Thus the two actual rectangles and both sides
use exactly the same exceptional predicate on the original row carrier.

The predicate is fixed before its ordinary restriction. On a row with
zero complete correlation its chosen value is immaterial, since the
original row coefficient is zero. No ordinary-row witness or previously
constructed normalized family is used in this definition.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

namespace CanonicalLiteralAllocatedData

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- The complete original character, including all fixed phases and
the active second factor, before any profile or capacity choice. -/
def rowCharacter (u : HeckeGeneral.Analysis.NonzeroIdeal K) : HeckeCharacter K :=
  correction *
    ((HeckeSkeleton.Moments.EngineStepV2.OriginalMovingFactors.appendSecondFactor (F.moving P R oldMoving)) C p leftMultiplicity rightMultiplicity
      pattern).character *
    completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ν u

variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (parent : MomentData K ω ψ) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

@[simp] theorem data_rowCharacter (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).rowCharacter u =
        rowCharacter P R F oldMoving correction C p leftMultiplicity rightMultiplicity
          pattern ν u := rfl

@[simp] theorem data_theta (ξ : WithLp 2 (ℝ × ℝ)) :
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative ξ).theta =
        parent.theta := rfl

end CanonicalLiteralAllocatedData

namespace PairedFiniteCharacters

/-- Equal actual row characters need only the identity correction.
The original finite theta set is not enlarged or assumed to be a group. -/
def diagonal {H : Type*} (theta : Finset (HeckeCharacter K))
    (character : H → HeckeCharacter K) : PairedFiniteCharacters theta H where
  subgroup := ⊥
  action χ hχ := by
    have h : χ = 1 := Subgroup.mem_bot.mp hχ
    subst χ
    exact ActualThetaAction.one (theta := theta)
  left := character
  right := character
  ratio_mem h := by simp only [div_self, Subgroup.one_mem]

end PairedFiniteCharacters

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- Only the original complete-correlation carrier is inspected. -/
def literalCharacter (h : H) : HeckeCharacter K :=
  if hh : h ∈ S.live then
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C S.primes
      S.leftMultiplicity S.rightMultiplicity pattern ν (S.extractedRow C ⟨h, hh⟩).momentIdeal
  else 1

def literalFiniteCharacters (theta : Finset (HeckeCharacter K)) :
    PairedFiniteCharacters theta H :=
  PairedFiniteCharacters.diagonal theta
    ((HeckeSkeleton.Moments.EngineStepV2.ActualSecondCorrelationRows.literalCharacter S) C P R F oldMoving correction pattern ν)

/-- Reweighting and two exact row restrictions leave the arithmetic
ideal and the character used in the original predicate unchanged. -/
theorem literalCharacter_reweighted
    (weight : H → ℂ) (keep₁ keep₂ : H → Prop)
    (h : ((({ S with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) :
    let T := (({ S with weight := weight }).restrictRows keep₁).restrictRows keep₂
    CanonicalLiteralAllocatedData.rowCharacter P R F oldMoving correction C T.primes
      T.leftMultiplicity T.rightMultiplicity pattern ν (T.extractedRow C h).momentIdeal =
      (HeckeSkeleton.Moments.EngineStepV2.ActualSecondCorrelationRows.literalCharacter S) C P R F oldMoving correction pattern ν h.val := by
  sorry

end ActualSecondCorrelationRows
end HeckeSkeleton.Moments.EngineStepV2

end

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

/-- The first Fourier coordinate is conjugated on the right side. -/
def SecondColumnSide.literalNegative : SecondColumnSide → Bool
  | .left => false
  | .right => true

end HeckeSkeleton.Moments.EngineStepV2

