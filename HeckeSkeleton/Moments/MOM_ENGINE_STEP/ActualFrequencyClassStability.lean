import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondSaving

/-!
# Genuine divided-frequency classes fix both extracted radicals

The unit/nonunit alternatives concern the frequency after the actual
common prime power has been divided out. Raw prime divisibility of the
undivided frequency does not determine this partition.

On the live complete correlation, changing its original generators
preserves nonvanishing. The actual local partition therefore proves
that its nonunit flags determine the unit flags as well. Equality of
these original flags fixes both radicals, the actual extraction element
and its norm factor, before any child or Fourier parameter is chosen.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The complement is taken only inside equal, non-six-divisible
multiplicities and on a genuinely nonzero local correlation. -/
theorem unitFrequencySaving_iff_nonunit_complement
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R)
    (hne : actualPrimePowerCorrelation C p m n h ≠ 0) :
    unitFrequencySaving C p m n h ↔
      m = n ∧ ¬6 ∣ m ∧ ¬nonunitFrequencySaving C p m n h :=
  actual_unitFrequencySaving_iff C p m n h hne

namespace ActualSecondCorrelationRows

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)

/-- The local nonvanishing is derived from the original full
correlation with its actual generators, not assumed on new columns. -/
theorem live_localCorrelation_ne_zero (h : R.live) (i : ι) :
    actualPrimePowerCorrelation C (R.primes i)
      (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ≠ 0 :=
  R.live_local_correlation_nonzero C h i

theorem live_unitSaving_iff_nonunit_complement (h : R.live) (i : ι) :
    unitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ↔
      R.leftMultiplicity i = R.rightMultiplicity i ∧ ¬6 ∣ R.leftMultiplicity i ∧
        ¬nonunitFrequencySaving C (R.primes i)
          (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) :=
  unitFrequencySaving_iff_nonunit_complement C (R.primes i)
    (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val)
    (R.live_localCorrelation_ne_zero C h i)

/-- A genuine class records the nonunit predicate after division by
the common prime power. On live rows this fixes both ideal radicals. -/
theorem frequencyRadicals_eq_of_nonunitClassification (h h' : R.live)
    (hsame : ∀ i, nonunitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ↔
      nonunitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h'.val)) :
    unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h.val) =
        unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h'.val) ∧
      nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h.val) =
        nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h'.val) := by
  have hunit (i : ι) : unitFrequencySaving C (R.primes i)
      (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ↔
      unitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h'.val) := by
    rw [R.live_unitSaving_iff_nonunit_complement C h i,
      R.live_unitSaving_iff_nonunit_complement C h' i, hsame i]
  constructor
  · unfold unitFrequencyRadical
    apply congrArg (primePowerProduct R.primes)
    funext i
    rw [hunit i]
  · unfold nonunitFrequencyRadical
    apply congrArg (primePowerProduct R.primes)
    funext i
    rw [hsame i]

/-- The generated extraction factor itself, not only its ideal or
norm, is fixed by the same actual nonunit flags. -/
theorem factor_eq_of_nonunitClassification (h h' : R.live)
    (hsame : ∀ i, nonunitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ↔
      nonunitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h'.val)) :
    R.factor C h.val = R.factor C h'.val := by
  unfold factor nonunitFrequencyGenerator
  apply congrArg (fun x =>
    primePowerProductGenerator C R.primes
      (fun i => min (R.leftMultiplicity i) (R.rightMultiplicity i)) * x)
  apply congrArg (primePowerProductGenerator C R.primes)
  funext i
  rw [hsame i]

theorem normFactor_eq_of_nonunitClassification (h h' : R.live)
    (hsame : ∀ i, nonunitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ↔
      nonunitFrequencySaving C (R.primes i)
        (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h'.val)) :
    R.normFactor C h.val = R.normFactor C h'.val := by
  unfold normFactor
  rw [(R.frequencyRadicals_eq_of_nonunitClassification C h h' hsame).2]

end ActualSecondCorrelationRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.unitFrequencySaving_iff_nonunit_complement
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.live_localCorrelation_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.frequencyRadicals_eq_of_nonunitClassification
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.factor_eq_of_nonunitClassification
