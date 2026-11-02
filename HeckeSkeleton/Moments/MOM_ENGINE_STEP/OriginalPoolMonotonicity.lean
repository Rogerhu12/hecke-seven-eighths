import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolAllowanceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

set_option linter.unusedSectionVars false

/-!
# One uniform pool bound for varying original row and frozen windows

The original sources keep their own row and frozen exponents and their
own displayed density. Bounding those two exponents by fixed windows
only decreases the comparison density and increases the main
multiplicity. The original pool, tags, prime and valuation stay fixed.

These inequalities therefore pass a literal local source scalar to
the uniform amplified index without requiring equal exponents across
the common-support fibres and without averaging over a second pool.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

namespace PowerScaleExteriorPool

variable (P : PowerScaleExteriorPool A bad Z ell eps)

/-- Larger original norm windows remove at least as many eligible
primes from the same displayed lower density. -/
theorem rowDensity_antitone_windows
    {M B Mmax Bmax : ℝ} (hM : M ≤ Mmax) (hB : B ≤ Bmax) :
    P.rowDensity Mmax Bmax ≤ P.rowDensity M B := by
  sorry

theorem rowDensity_pos_of_uniform
    {M B Mmax Bmax : ℝ} (hM : M ≤ Mmax) (hB : B ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax) : 0 < P.rowDensity M B := by
  sorry

/-- The actual local reciprocal density is bounded by one common
positive comparison density, with the original factor four unchanged. -/
theorem four_div_rowDensity_le
    {M B Mmax Bmax : ℝ} (hM : M ≤ Mmax) (hB : B ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax) :
    4 / P.rowDensity M B ≤ 4 / P.rowDensity Mmax Bmax := by
  sorry

end PowerScaleExteriorPool

namespace AmplifiedCommonIndex

variable (P : PowerScaleExteriorPool A bad Z ell eps)
variable (main : TwoDivisorCommonBranch (K := K))
variable (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))

/-- The exact local scalar, including the main multiplicity, increases
when its two original norm windows are replaced by fixed upper bounds. -/
theorem originalTagWeight_mono_windows
    {M B Mmax Bmax : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ Mmax) (hB : B ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax) (i : AmplifiedCommonIndex P main error) :
    originalTagWeight P M B main error i ≤
      originalTagWeight P Mmax Bmax main error i := by
  sorry

/-- All common and divisor weights are nonnegative and unchanged. The
actual moving norm is retained in the same amplified arithmetic index. -/
theorem amplifiedIndexWeight_mono_windows
    {M B Mmax Bmax : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ Mmax) (hB : B ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax) (i : AmplifiedCommonIndex P main error) :
    amplifiedIndexWeight P M B main error i ≤
      amplifiedIndexWeight P Mmax Bmax main error i := by
  sorry

/-- A genuine original pointwise scalar with varying local windows
passes directly to the fixed-window index. Only the small error δ is
left outside; the pool length or moving-prime norm is paid internally. -/
theorem pointwise_of_original_tag_uniform
    {M B Mmax Bmax : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ Mmax) (hB : B ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax)
    (i : AmplifiedCommonIndex P main error)
    (actual C control remaining δ : ℝ) (hC : 0 ≤ C) (hcontrol : 0 ≤ control)
    (hremaining : remaining ≤ δ + movingLength P main error i)
    (hraw : actual ≤ C * control * originalTagWeight P M B main error i *
      Z ^ remaining * harmonicWeight P main error i) :
    actual ≤ C * control * Z ^ δ * amplifiedIndexWeight P Mmax Bmax main error i := by
  sorry

end AmplifiedCommonIndex
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PowerScaleExteriorPool.rowDensity_antitone_windows
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifiedCommonIndex.pointwise_of_original_tag_uniform
