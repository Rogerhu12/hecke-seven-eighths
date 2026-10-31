import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualMovingFrequencyFactors

/-!
# The complete second deletion support from its actual factors

The active moving element is the original singleton produced by the
sixth/active split of the extracted frequency. Its prime exponents are
at most six, and a nonzero exponent belongs to one of the actual unit
or nonunit frequency supports. These local facts prove the individual
generated-ideal divisibility required by `SupportAtoms`.

The sixth root is not discarded. It is multiplied into both the old
support ideal and the original remaining deletion ideal. The latter
keeps exactly the original remaining zeros and the sixth-root zeros.
Its full support and norm window are conclusions; no completed support
divisibility or joint child-row budget is assumed. The logarithmic cost
of the complete sixth root remains explicit in the norm window.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- This is the bound for every finite pattern, before choosing a row. -/
theorem secondActiveExponent_le_six (m n : ι → ℕ) (pattern : ι → Bool) (i : ι) :
    secondActiveExponent m n pattern i ≤ 6 := by
  have hrem := Nat.mod_lt (min (m i) (n i)) (by decide : 0 < 6)
  unfold secondActiveExponent
  split <;> omega

private theorem second_active_exponent_le_indicators
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) (i : ι) (hm : 0 < m i) (hn : 0 < n i)
    (hne : actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    secondActiveExponent m n (actualNonunitPattern C p m n h) i ≤
      (if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) * 6 +
        (if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) * 6 := by
  have hbound := secondActiveExponent_le_six m n (actualNonunitPattern C p m n h) i
  by_cases hu : unitFrequencySaving C (p i) (m i) (n i) h
  · simp only [if_pos hu, one_mul]
    omega
  by_cases hv : nonunitFrequencySaving C (p i) (m i) (n i) h
  · simpa only [if_neg hu, if_pos hv, zero_mul, one_mul, zero_add] using hbound
  have hz : secondActiveExponent m n (actualNonunitPattern C p m n h) i = 0 := by
    by_contra hactive
    rcases (secondActiveExponent_ne_zero_iff C p m n h i hm hn hne).mp hactive with hu' | hv'
    · exact hu hu'
    · exact hv hv'
  rw [hz]
  exact Nat.zero_le _

/-- Divisibility of the full original active ideal, before taking a
radical. It is derived one prime power at a time from the actual local
correlation; no whole-support divisor hypothesis is used. -/
theorem secondActiveFrequencyIdeal_dvd_radical_powers
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    (secondActiveFrequencyIdeal p m n (actualNonunitPattern C p m n h)).val ∣
      (unitFrequencyRadical C p m n h).val ^ 6 *
        (nonunitFrequencyRadical C p m n h).val ^ 6 := by
  change (∏ i, (p i).val.asIdeal ^
      secondActiveExponent m n (actualNonunitPattern C p m n h) i) ∣
    (∏ i, (p i).val.asIdeal ^
      (if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)) ^ 6 *
      (∏ i, (p i).val.asIdeal ^
        (if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)) ^ 6
  calc
    _ ∣ ∏ i, (p i).val.asIdeal ^
        ((if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) * 6 +
          (if nonunitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) * 6) := by
      apply Finset.prod_dvd_prod_of_dvd
      intro i _
      exact pow_dvd_pow _
        (second_active_exponent_le_indicators C p m n h i (hm i) (hn i) (hne i))
    _ = _ := by
      simp only [pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_pow]

/-- The same exterior sixth-root ideal in the original moment's
nonzero-ideal type. Its underlying ideal is unchanged. -/
def secondSixthRootNonzeroIdeal (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  (HeckeAxiom.exteriorEquiv A (secondSixthRootIdeal p m n)).val

@[simp] theorem secondSixthRootNonzeroIdeal_val (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    (secondSixthRootNonzeroIdeal p m n).val = (secondSixthRootIdeal p m n).val := rfl

/-- Multiplication of the remaining ideal retains both actual deletion
conditions; it is not a deletion of a sixth-power character at its zeros. -/
theorem secondFullDeletion_coprime
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (J : Ideal (𝓞 K)) :
    IsCoprime J (remaining * secondSixthRootNonzeroIdeal p m n).val ↔
      IsCoprime J remaining.val ∧ IsCoprime J (secondSixthRootIdeal p m n).val :=
  IsCoprime.mul_right_iff

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- All fields are supplied by the original singleton element and its
actual generated ideal. The old support is enlarged by the complete
sixth root, and the remaining ideal receives that very same factor. -/
def secondOriginalMovingSupportAtoms
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val) :
    (secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h)).SupportAtoms
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal p m n))
      (unitFrequencyRadical C p m n h) (nonunitFrequencyRadical C p m n h)
      (remaining * secondSixthRootNonzeroIdeal p m n) where
  ideal _ := secondActiveFrequencyIdeal p m n (actualNonunitPattern C p m n h)
  generates _ := secondActiveFrequencyGenerator_generates C p m n (actualNonunitPattern C p m n h)
  oldPower _ := 0
  unitPower _ := 6
  nonunitPower _ := 6
  factor_divides _ := by
    simpa only [pow_zero, one_mul] using
      secondActiveFrequencyIdeal_dvd_radical_powers C p m n hm hn h hne
  remaining_divides := by
    change remaining.val * (secondSixthRootIdeal p m n).val ∣
      (old.val * (secondSixthRootIdeal p m n).val) *
        (unitFrequencyRadical C p m n h).val * (nonunitFrequencyRadical C p m n h).val
    have hd : remaining.val * (secondSixthRootIdeal p m n).val ∣
        old.val * (secondSixthRootIdeal p m n).val :=
      mul_dvd_mul hremaining (dvd_refl _)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _

/-- The enlarged old-support window pays the norm of the complete sixth
root. This is its literal logarithmic length, with no lower-window
substitution or omitted multiplicity. -/
theorem secondOldWithSixthRoot_norm_window
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (old : A.Exterior)
    (Z oldLength : ℝ) (hZ : 1 < Z) (hold : A.exteriorNorm old ≤ Z ^ oldLength) :
    A.exteriorNorm (ExteriorIdealEuler.mul old (secondSixthRootIdeal p m n)) ≤
      Z ^ (oldLength + idealLogLength Z (secondSixthRootIdeal p m n).val) := by
  change (Ideal.absNorm (old.val * (secondSixthRootIdeal p m n).val) : ℝ) ≤ _
  rw [map_mul, Nat.cast_mul, Real.rpow_add (zero_lt_one.trans hZ),
    rpow_idealLogLength Z hZ _ (secondSixthRootIdeal p m n).property.1]
  exact mul_le_mul_of_nonneg_right hold (Nat.cast_nonneg _)

/-- The actual complete child support, with sixth-root deletion kept,
is bounded from the original old ideal's window. -/
theorem secondFullDeletion_support_norm_window
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val)
    (Z oldLength : ℝ) (hZ : 1 < Z) (hold : A.exteriorNorm old ≤ Z ^ oldLength) :
    idealNorm K
        ((secondOriginalMovingFactors P R C p m n (actualNonunitPattern C p m n h)).fullMaskSupport
          (remaining * secondSixthRootNonzeroIdeal p m n)) ≤
      Z ^ (oldLength + idealLogLength Z (secondSixthRootIdeal p m n).val +
        idealLogLength Z (unitFrequencyRadical C p m n h).val +
        idealLogLength Z (nonunitFrequencyRadical C p m n h).val) := by
  let W := secondOriginalMovingSupportAtoms P R C p m n hm hn h hne old remaining hremaining
  exact W.fullMaskSupport_norm_window Z
    (oldLength + idealLogLength Z (secondSixthRootIdeal p m n).val)
    (idealLogLength Z (unitFrequencyRadical C p m n h).val)
    (idealLogLength Z (nonunitFrequencyRadical C p m n h).val)
    (zero_lt_one.trans hZ)
    (secondOldWithSixthRoot_norm_window p m n old Z oldLength hZ hold)
    (rpow_idealLogLength Z hZ _ (unitFrequencyRadical C p m n h).property.1).symm.le
    (rpow_idealLogLength Z hZ _ (nonunitFrequencyRadical C p m n h).property.1).symm.le

namespace ActualSecondCorrelationRows

variable {H : Type*} (S : ActualSecondCorrelationRows A σ H ι)

/-- Every local nonvanishing premise is discharged by the original
live row and its original, possibly noncanonical, pair of generators. -/
def fullDeletionSupportAtoms
    (C : A.GeneralArithmeticContext σ η hS)
    (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val) (h : S.live) :
    (secondOriginalMovingFactors P R C S.primes S.leftMultiplicity S.rightMultiplicity
      (actualNonunitPattern C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val))).SupportAtoms
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal S.primes S.leftMultiplicity S.rightMultiplicity))
      (unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val))
      (nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val))
      (remaining * secondSixthRootNonzeroIdeal S.primes S.leftMultiplicity S.rightMultiplicity) :=
  secondOriginalMovingSupportAtoms P R C S.primes S.leftMultiplicity S.rightMultiplicity
    hm hn (S.frequency h.val) (S.live_local_correlation_nonzero C h) old remaining hremaining

/-- On an actual nonunit-pattern class the original moving list is
fixed before the row and all Fourier variables. The support certificate
uses each row's actual unit/nonunit radicals without changing that list. -/
def nonunitClassFullDeletionSupportAtoms
    (C : A.GeneralArithmeticContext σ η hS)
    (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
    (old : A.Exterior) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hremaining : remaining.val ∣ old.val) (pattern : ι → Bool) (h : S.NonunitClass C pattern) :
    (secondOriginalMovingFactors P R C S.primes S.leftMultiplicity S.rightMultiplicity pattern).SupportAtoms
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal S.primes S.leftMultiplicity S.rightMultiplicity))
      (unitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val))
      (nonunitFrequencyRadical C S.primes S.leftMultiplicity S.rightMultiplicity (S.frequency h.val.val))
      (remaining * secondSixthRootNonzeroIdeal S.primes S.leftMultiplicity S.rightMultiplicity) := by
  have W := S.fullDeletionSupportAtoms P R C hm hn old remaining hremaining h.val
  rw [h.property] at W
  exact W

end ActualSecondCorrelationRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.secondActiveFrequencyIdeal_dvd_radical_powers
#print axioms HeckeSkeleton.Moments.EngineStep.secondFullDeletion_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.secondOriginalMovingSupportAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.secondOldWithSixthRoot_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.secondFullDeletion_support_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.fullDeletionSupportAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.nonunitClassFullDeletionSupportAtoms
