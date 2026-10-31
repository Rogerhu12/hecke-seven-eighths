import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationSupport

/-!
# Exchange the two columns of the actual correlation source

The same original rows, prime dictionary and original ideals are kept.
The two multiplicities and chosen generators exchange places, while the
actual frequency is negated.  This negation preserves the generated
original ideal.  The complete correlation is then exactly conjugated,
so conjugating the original row weight preserves its full magnitude.

No residual ideal or child is reselected here.  These source identities
allow the smaller of the two original common sides to be used later.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)

/-- Exchange the literal left and right column data.  Only the original
frequency and row weight change, by negation and conjugation. -/
def swapColumns : ActualSecondCorrelationRows A σ H ι where
  primes := R.primes
  primes_injective := R.primes_injective
  leftMultiplicity := R.rightMultiplicity
  rightMultiplicity := R.leftMultiplicity
  leftGenerator := R.rightGenerator
  rightGenerator := R.leftGenerator
  leftGenerates := R.rightGenerates
  rightGenerates := R.leftGenerates
  rows := R.rows
  originalIdeal := R.originalIdeal
  frequency h := -R.frequency h
  generates h hh := by
    refine ⟨neg_ne_zero.mpr (R.generates h hh).1, ?_⟩
    simpa only [Ideal.span_singleton_neg] using (R.generates h hh).2
  weight h := star (R.weight h)

@[simp] theorem swapColumns_primes : R.swapColumns.primes = R.primes := rfl

@[simp] theorem swapColumns_leftMultiplicity :
    R.swapColumns.leftMultiplicity = R.rightMultiplicity := rfl

@[simp] theorem swapColumns_rightMultiplicity :
    R.swapColumns.rightMultiplicity = R.leftMultiplicity := rfl

@[simp] theorem swapColumns_leftGenerator :
    R.swapColumns.leftGenerator = R.rightGenerator := rfl

@[simp] theorem swapColumns_rightGenerator :
    R.swapColumns.rightGenerator = R.leftGenerator := rfl

@[simp] theorem swapColumns_rows : R.swapColumns.rows = R.rows := rfl

@[simp] theorem swapColumns_originalIdeal :
    R.swapColumns.originalIdeal = R.originalIdeal := rfl

@[simp] theorem swapColumns_frequency (h : H) :
    R.swapColumns.frequency h = -R.frequency h := rfl

@[simp] theorem swapColumns_weight (h : H) :
    R.swapColumns.weight h = star (R.weight h) := rfl

/-- The original complete quotients, rather than a primitive substitute,
give exact conjugation at the negated original frequency. -/
@[simp] theorem swapColumns_correlation (h : H) :
    R.swapColumns.correlation h = star (R.correlation h) := by
  change generatedIdealCorrelation (σ := σ)
      (primePowerProduct R.primes R.rightMultiplicity)
      (primePowerProduct R.primes R.leftMultiplicity)
      R.rightGenerator R.leftGenerator R.rightGenerates R.leftGenerates (-R.frequency h) =
    star (generatedIdealCorrelation (σ := σ)
      (primePowerProduct R.primes R.leftMultiplicity)
      (primePowerProduct R.primes R.rightMultiplicity)
      R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates (R.frequency h))
  simpa only [neg_neg] using generatedIdealCorrelation_swap (σ := σ)
    (primePowerProduct R.primes R.rightMultiplicity)
    (primePowerProduct R.primes R.leftMultiplicity)
    R.rightGenerator R.leftGenerator R.rightGenerates R.leftGenerates (-R.frequency h)

@[simp] theorem swapColumns_correlation_norm (h : H) :
    ‖R.swapColumns.correlation h‖ = ‖R.correlation h‖ := by
  rw [R.swapColumns_correlation h, norm_star]

/-- The actual carrier of nonzero correlations is unchanged. -/
@[simp] theorem swapColumns_live : R.swapColumns.live = R.live := by
  simp only [live, swapColumns_rows, swapColumns_correlation, star_ne_zero]

/-- Conjugation applies to the complete original row coefficient,
including its correlation, before any absolute value is taken. -/
@[simp] theorem swapColumns_weight_correlation (h : H) :
    R.swapColumns.weight h * R.swapColumns.correlation h =
      star (R.weight h * R.correlation h) := by
  rw [R.swapColumns_weight h, R.swapColumns_correlation h, star_mul']

@[simp] theorem swapColumns_weight_correlation_norm (h : H) :
    ‖R.swapColumns.weight h * R.swapColumns.correlation h‖ =
      ‖R.weight h * R.correlation h‖ := by
  rw [R.swapColumns_weight_correlation h, norm_star]

end ActualSecondCorrelationRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapColumns
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapColumns_correlation
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapColumns_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapColumns_weight_correlation_norm
