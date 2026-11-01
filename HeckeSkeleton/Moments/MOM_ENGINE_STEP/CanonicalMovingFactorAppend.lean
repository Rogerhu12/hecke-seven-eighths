import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPatternChildWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RemainingMaskRadical

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

namespace HeckeSkeleton.Moments.EngineStep

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

@[simp] theorem appendFactors_count : (D.appendFactors E).count = D.count + E.count := rfl

@[simp] theorem appendFactors_element_left (i : Fin D.count) :
    (D.appendFactors E).element (Fin.castAdd E.count i) = D.element i :=
  Fin.append_left _ _ _

@[simp] theorem appendFactors_element_right (i : Fin E.count) :
    (D.appendFactors E).element (Fin.natAdd D.count i) = E.element i :=
  Fin.append_right _ _ _

@[simp] theorem appendFactors_power_left (i : Fin D.count) :
    (D.appendFactors E).power (Fin.castAdd E.count i) = D.power i :=
  Fin.append_left _ _ _

@[simp] theorem appendFactors_power_right (i : Fin E.count) :
    (D.appendFactors E).power (Fin.natAdd D.count i) = E.power i :=
  Fin.append_right _ _ _

@[simp] theorem appendFactors_decomposition_left (i : Fin D.count) :
    (D.appendFactors E).decomposition (Fin.castAdd E.count i) = D.decomposition i := by
  simp only [decomposition, orbit, appendFactors_element_left]

@[simp] theorem appendFactors_decomposition_right (i : Fin E.count) :
    (D.appendFactors E).decomposition (Fin.natAdd D.count i) = E.decomposition i := by
  simp only [decomposition, orbit, appendFactors_element_right]

@[simp] theorem appendFactors_factorIdeal_left (i : Fin D.count) :
    (D.appendFactors E).factorIdeal (Fin.castAdd E.count i) = D.factorIdeal i := by
  simp only [factorIdeal, appendFactors_decomposition_left]

@[simp] theorem appendFactors_factorIdeal_right (i : Fin E.count) :
    (D.appendFactors E).factorIdeal (Fin.natAdd D.count i) = E.factorIdeal i := by
  simp only [factorIdeal, appendFactors_decomposition_right]

@[simp] theorem appendFactors_factorCharacter_left (i : Fin D.count) :
    (D.appendFactors E).factorCharacter (Fin.castAdd E.count i) = D.factorCharacter i := by
  simp only [factorCharacter, appendFactors_decomposition_left]

@[simp] theorem appendFactors_factorCharacter_right (i : Fin E.count) :
    (D.appendFactors E).factorCharacter (Fin.natAdd D.count i) = E.factorCharacter i := by
  simp only [factorCharacter, appendFactors_decomposition_right]

theorem appendFactors_character :
    (D.appendFactors E).character = D.character * E.character := by
  change (∏ i : Fin (D.count + E.count),
    (D.appendFactors E).factorCharacter i ^ (D.appendFactors E).power i) = _
  rw [Fin.prod_univ_add]
  simp only [appendFactors_factorCharacter_left, appendFactors_factorCharacter_right,
    appendFactors_power_left, appendFactors_power_right]
  rfl

theorem appendFactors_fullIdeal_val :
    (D.appendFactors E).fullIdeal.val = D.fullIdeal.val * E.fullIdeal.val := by
  change (∏ i : Fin (D.count + E.count), ((D.appendFactors E).factorIdeal i).val) = _
  rw [Fin.prod_univ_add]
  simp only [appendFactors_factorIdeal_left, appendFactors_factorIdeal_right]
  rfl

theorem appendFactors_fullIdeal :
    (D.appendFactors E).fullIdeal = ExteriorIdealEuler.mul D.fullIdeal E.fullIdeal :=
  Subtype.ext (D.appendFactors_fullIdeal_val E)

/-- No coprimality or distinction between the two lists is required. -/
theorem appendFactors_support_primes :
    primeSupport (D.appendFactors E).support.val =
      primeSupport D.support.val ∪ primeSupport E.support.val := by
  rw [(D.appendFactors E).support_primes, D.appendFactors_fullIdeal_val E,
    D.support_primes, E.support_primes]
  simp only [primeSupport, normalizedFactors_mul D.fullIdeal.property.1 E.fullIdeal.property.1,
    Multiset.toFinset_add]

/-- The displayed radical retains every original prime even if its
integer character exponent is zero or cancels another occurrence. -/
theorem appendFactors_support_val :
    (D.appendFactors E).support.val =
      commonRadical (D.support.val * E.support.val) (D.support.val * E.support.val) := by
  rw [← squarefree_support_product_self (D.appendFactors E).support_squarefree,
    D.appendFactors_support_primes E]
  simp only [commonRadical, Finset.inter_self, primeSupport,
    normalizedFactors_mul D.support.property.1 E.support.property.1,
    Multiset.toFinset_add]

theorem appendFactors_support_coprime_iff (I : Ideal (𝓞 K)) :
    IsCoprime I (D.appendFactors E).support.val ↔
      IsCoprime I D.support.val ∧ IsCoprime I E.support.val := by
  rw [(D.appendFactors E).coprime_support_iff_fullIdeal I,
    D.appendFactors_fullIdeal_val E, IsCoprime.mul_right_iff,
    ← D.coprime_support_iff_fullIdeal I, ← E.coprime_support_iff_fullIdeal I]

theorem appendFactors_fullMaskSupport_primes
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    primeSupport ((D.appendFactors E).fullMaskSupport remaining).val =
      (primeSupport D.support.val ∪ primeSupport E.support.val) ∪
        primeSupport remaining.val := by
  rw [(D.appendFactors E).fullMaskSupport_primes remaining, D.appendFactors_support_primes E]

theorem appendFactors_fullMaskSupport_coprime_iff
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    IsCoprime I ((D.appendFactors E).fullMaskSupport remaining).val ↔
      (IsCoprime I D.support.val ∧ IsCoprime I E.support.val) ∧
        IsCoprime I remaining.val := by
  rw [(D.appendFactors E).fullMaskSupport_coprime_iff remaining I,
    D.appendFactors_support_coprime_iff E I]

private theorem appended_mask_reorder (a b c d e : Bool) :
    ((a && (b && c)) && (d && e)) = ((((a && b) && d) && c) && e) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

/-- On the original complete-row gate the new mask is exactly the
old full mask, the appended factor mask and the full remaining-factor
mask. Normalizing the old remaining ideal deletes no effective zero. -/
theorem appendFactors_normalizedFullMask
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (F : A.Exterior) (I : Ideal (𝓞 K)) :
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I (D.appendFactors E).support.val)) &&
      decide (IsCoprime I (remainingMaskIdeal A remaining * exteriorMomentIdeal F).val)) =
    ((((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I D.support.val)) && decide (IsCoprime I remaining.val)) &&
      decide (IsCoprime I E.support.val)) && decide (IsCoprime I F.val)) := by
  change ((_ && decide (IsCoprime I (D.appendFactors E).support.val)) &&
    decide (IsCoprime I ((remainingMaskIdeal A remaining).val * F.val))) = _
  rw [D.appendFactors_support_coprime_iff E I, IsCoprime.mul_right_iff]
  simp only [Bool.decide_and]
  exact (appended_mask_reorder _ _ _ _ _).trans
    (congrArg (fun gate : Bool =>
      (gate && decide (IsCoprime I E.support.val)) && decide (IsCoprime I F.val))
      (completeMovingMask_remainingRadical A remaining u I
        (decide (IsCoprime I D.support.val))).symm)

theorem appendFactors_normalizedFullMask_primes
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (F : A.Exterior) :
    primeSupport ((D.appendFactors E).fullMaskSupport
        (remainingMaskIdeal A remaining * exteriorMomentIdeal F)).val =
      (primeSupport D.support.val ∪ primeSupport E.support.val) ∪
        ((primeSupport remaining.val \ primeSupport A.cS) ∪ primeSupport F.val) := by
  rw [D.appendFactors_fullMaskSupport_primes E]
  have hprod : primeSupport ((remainingMaskIdeal A remaining).val * F.val) =
      primeSupport (remainingMaskIdeal A remaining).val ∪ primeSupport F.val := by
    simp only [primeSupport, normalizedFactors_mul
      (nonZeroDivisors.ne_zero (remainingMaskIdeal A remaining).property) F.property.1,
      Multiset.toFinset_add]
  change (primeSupport D.support.val ∪ primeSupport E.support.val) ∪
    primeSupport ((remainingMaskIdeal A remaining).val * F.val) = _
  rw [hprod, remainingMaskIdeal_val, remainingMaskRadical_primes]

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
    (D.appendFactors E).SupportAtoms old unit nonunit remaining where
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
  D.appendFactors (secondOriginalMovingFactors P Rchar C p m n pattern)

@[simp] theorem appendSecondFactor_count
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    (D.appendSecondFactor C p m n pattern).count = D.count + 1 := rfl

theorem appendSecondFactor_character
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    (D.appendSecondFactor C p m n pattern).character =
      D.character * (secondOriginalMovingFactors P Rchar C p m n pattern).character :=
  D.appendFactors_character _

theorem appendSecondFactor_support_primes
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    primeSupport (D.appendSecondFactor C p m n pattern).support.val =
      primeSupport D.support.val ∪
        primeSupport (secondOriginalMovingFactors P Rchar C p m n pattern).support.val :=
  D.appendFactors_support_primes _

/-- Both old and new generator dictionaries are constructed from
their actual elements. The normalization of the original remaining
ideal is exact behind the complete-row mask, and the sixth root stays
in the new remaining ideal with its full multiplicity. -/
def appendSecondFullDeletionSupportAtoms
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    (D.appendSecondFactor C p m n (actualNonunitPattern C p m n h)).SupportAtoms
      (ExteriorIdealEuler.mul (D.effectiveFullSupport remaining) (secondSixthRootIdeal p m n))
      (unitFrequencyRadical C p m n h) (nonunitFrequencyRadical C p m n h)
      (remainingMaskIdeal A remaining * secondSixthRootNonzeroIdeal p m n) :=
  ((D.effectiveSupportAtoms remaining
      (unitFrequencyRadical C p m n h) (nonunitFrequencyRadical C p m n h)).withRemainingFactor
        (secondSixthRootIdeal p m n)).appendFactors
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
        ((D.appendSecondFactor C p m n (actualNonunitPattern C p m n h)).fullMaskSupport
          (remainingMaskIdeal A remaining * secondSixthRootNonzeroIdeal p m n)) ≤
      Z ^ (idealLogLength Z (D.effectiveFullSupport remaining).val +
        idealLogLength Z (secondSixthRootIdeal p m n).val +
        idealLogLength Z (unitFrequencyRadical C p m n h).val +
        idealLogLength Z (nonunitFrequencyRadical C p m n h).val) := by
  let W := D.appendSecondFullDeletionSupportAtoms remaining C p m n hm hn h hne
  exact W.fullMaskSupport_norm_window Z
    (idealLogLength Z (D.effectiveFullSupport remaining).val +
      idealLogLength Z (secondSixthRootIdeal p m n).val)
    (idealLogLength Z (unitFrequencyRadical C p m n h).val)
    (idealLogLength Z (nonunitFrequencyRadical C p m n h).val)
    (zero_lt_one.trans hZ)
    (secondOldWithSixthRoot_norm_window p m n (D.effectiveFullSupport remaining) Z
      (idealLogLength Z (D.effectiveFullSupport remaining).val) hZ
      (rpow_idealLogLength Z hZ _ (D.effectiveFullSupport remaining).property.1).symm.le)
    (rpow_idealLogLength Z hZ _ (unitFrequencyRadical C p m n h).property.1).symm.le
    (rpow_idealLogLength Z hZ _ (nonunitFrequencyRadical C p m n h).property.1).symm.le

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
    (oldMoving.appendSecondFactor C S.primes S.leftMultiplicity S.rightMultiplicity pattern).SupportAtoms
      (ExteriorIdealEuler.mul (oldMoving.effectiveFullSupport remaining)
        (secondSixthRootIdeal S.primes S.leftMultiplicity S.rightMultiplicity))
      (unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val))
      (nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val))
      (remainingMaskIdeal A remaining *
        secondSixthRootNonzeroIdeal S.primes S.leftMultiplicity S.rightMultiplicity) := by
  have W := oldMoving.appendSecondFullDeletionSupportAtoms remaining C S.primes
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
    (data parent (oldMoving.appendFactors newMoving) correction hcorr sector remaining budget
      inverse left right geometry index).rowCharacter u =
      (correction * oldMoving.character * newMoving.character) *
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P Rchar (sector u) u := by
  change (correction * (oldMoving.appendFactors newMoving).character) * _ = _
  simp only [oldMoving.appendFactors_character newMoving, mul_assoc]

/-- This is the literal mask of the same canonical child, with no
new mask equality supplied by its caller. -/
theorem appended_commonMask (F : A.Exterior)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    (data parent (oldMoving.appendFactors newMoving) correction hcorr sector
      (remainingMaskIdeal A remaining * exteriorMomentIdeal F) budget
      inverse left right geometry index).commonMask u I =
    ((((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I oldMoving.support.val)) && decide (IsCoprime I remaining.val)) &&
      decide (IsCoprime I newMoving.support.val)) && decide (IsCoprime I F.val)) :=
  oldMoving.appendFactors_normalizedFullMask newMoving remaining u F I

end CanonicalOriginalChildData

private theorem appendedFactors_width_shift
    (Z a₀ q wo krow g r : ℝ) (I J T V : Ideal (𝓞 K)) :
    secondCommonChildWidth Z a₀ (q + r) wo krow g I J T V =
      secondCommonChildWidth Z a₀ q wo krow g I J T V + r := by
  unfold secondCommonChildWidth
  ring

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
    (hclass : chart.NonunitLabelStable)
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
    let pattern := chart.originalNonunitPattern ∅ X hX label
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K
          ((oldMoving.appendSecondFactor C b.primes b.leftMultiplicity b.rightMultiplicity pattern).fullMaskSupport
            (remainingMaskIdeal A remaining *
              secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  dsimp only
  let S := chart.actualRows ∅ X hX label
  let pattern := chart.originalNonunitPattern ∅ X hX label
  let hp := chart.originalNonunitClass hclass ∅ X hX label h
  let r₆ := idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val
  let old := oldMoving.effectiveFullSupport remaining
  let W := S.appendedNonunitClassSupportAtoms oldMoving remaining C
    b.left_positive b.right_positive pattern hp
  have holdRoot : A.exteriorNorm
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ ((q + r₆) + wo) := by
    have hroot := secondOldWithSixthRoot_norm_window b.primes b.leftMultiplicity b.rightMultiplicity
      old Z (q + wo) hZ hold
    change A.exteriorNorm
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
        Z ^ ((q + wo) + r₆) at hroot
    rwa [show (q + wo) + r₆ = (q + r₆) + wo by ring] at hroot
  have hjoint := chart.actualRows_empty_extracted_fullJoint_window X hX label
    retainedScale Z g a₀ (q + r₆) wo cutoffExponent hscale hZ hradius hcutoff hleft hright
    (oldMoving.appendSecondFactor C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
    (remainingMaskIdeal A remaining *
      secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))
    holdRoot h W
  have hunit := S.secondPatternUnitIdeal_eq_live C pattern h hp.property
  have hnonunit := S.secondPatternNonunitIdeal_eq C pattern h.val hp.property
  change secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern =
    unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val) at hunit
  change secondPatternNonunitIdeal b.primes pattern =
    nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val) at hnonunit
  rw [← hunit, ← hnonunit] at hjoint
  simpa only [appendedFactors_width_shift, r₆] using hjoint

/-- Every actual original live row enters this same child. The old
moving list, original finite correction, all tests and selected slots
are preserved; only the genuine second factor and root are appended. -/
theorem canonicalOriginalChild_allowed_of_appended_pattern
    (hclass : chart.NonunitLabelStable)
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
    let pattern := chart.originalNonunitPattern ∅ X hX label
    (CanonicalOriginalChildData.data parent
      (oldMoving.appendSecondFactor C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
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
  dsimp only
  refine ⟨(HeckeAxiom.exteriorEquiv A
    ((chart.actualRows ∅ X hX label).extractedRow C h).ideal).property, ?_⟩
  exact chart.actualRows_appended_pattern_fullDeletion_joint_window hclass oldMoving remaining
    X hX label retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff hleft hright hold h

end SecondBlockProfileChart
end ActualPatternWindows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendFactors_character
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendFactors_support_primes
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendSecondFullDeletionSupportAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendSecondFullDeletion_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendFactors_normalizedFullMask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData.appended_commonMask
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_appended_pattern_fullDeletion_joint_window
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalOriginalChild_allowed_of_appended_pattern
