import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPool

/-!
# The one actual pool of the primitive engine

The prime ideal theorem chooses this pool after the scale and before
every original column or divisor. Both Gauss sides and all four tags
use this same value. The zero-slot branch does not call this chooser.
All deletions in the later sources retain their actual complete ideals.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEnginePool

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.CenteredMomentCounting CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K]
variable (A : SArithmeticData K) (b : Box)

/-- This internal selection contains the actual pool and its raw density
facts. It is constructed from the prime ideal theorem, never supplied
as an assumption of the primitive engine. -/
structure Selection (Z : ℝ) where
  pool : PowerScaleExteriorPool A ∅ Z (b.step / 3) b.loss
  density_pos : 0 < pool.rowDensity b.rowBound b.columnBound
  inverse_density : 1 / pool.rowDensity b.rowBound b.columnBound ≤
    2 * Z ^ (-(b.step / 3) + b.loss)
  cardinal_mass : (pool.primes.card : ℝ) / pool.rowDensity b.rowBound b.columnBound ≤
    2 * idealCountConstant K * Z ^ b.loss
  error_mass : ∀ n : ℕ,
    (∑ p ∈ pool.primes, FirstGaussPoolData.localErrorWeight p n *
      Q p ^ amplifierMovingExponent n) / pool.rowDensity b.rowBound b.columnBound ≤
        2 * idealCountConstant K * Z ^ b.loss

theorem exists_threshold :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Nonempty (Selection A b Z) := by
  obtain ⟨Z₀, hZ₀, hpools⟩ := exists_uniform_original_pool A ∅
    (b.step / 3) b.loss b.rowBound b.columnBound
    (div_pos b.step_pos (by norm_num)) b.loss_pos b.pool_separation.2
    b.rowBound_nonneg b.columnBound_nonneg
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ
  obtain ⟨pool, hp⟩ := hpools Z hZ
  have h := hp b.rowBound b.columnBound le_rfl le_rfl
  exact ⟨⟨pool, h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The threshold is fixed before all moving data. -/
def threshold : ℝ := Classical.choose (exists_threshold A b)

theorem threshold_gt_one : 1 < threshold A b :=
  (Classical.choose_spec (exists_threshold A b)).1

/-- The sole call to the prime-pool choice in the positive-slot branch. -/
def selected (Z : ℝ) (hZ : threshold A b ≤ Z) : Selection A b Z :=
  Classical.choice ((Classical.choose_spec (exists_threshold A b)).2 Z hZ)

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEnginePool

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEnginePool.exists_threshold
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEnginePool.selected
