import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

/-!
# One original prime pool with uniform deletion costs

The prime ideal theorem chooses the actual pool once at each scale,
before the original columns, common blocks, physical frequencies, frozen
ideals, internal divisors, and Fourier variables.  Its one density pays
all of the actual error valuations.  The fixed threshold below combines
the original PIT threshold with the quantitative row-deletion threshold;
no positive-density or aggregate pool-mass certificate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

/-- The same actual pool works for every later row and frozen-ideal
window in the fixed box.  In particular both first Gauss sides and all
of their divisor pools use this one witness. -/
theorem exists_uniform_original_pool
    (A : SArithmeticData K) (bad : Finset (HeightOneSpectrum (𝓞 K)))
    (ell eps Mmax Bmax : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∃ pool : PowerScaleExteriorPool A bad Z ell eps,
        ∀ M B : ℝ, M ≤ Mmax → B ≤ Bmax →
          0 < pool.rowDensity M B ∧
          1 / pool.rowDensity M B ≤ 2 * Z ^ (-ell + eps) ∧
          (pool.primes.card : ℝ) / pool.rowDensity M B ≤
            2 * idealCountConstant K * Z ^ eps ∧
          ∀ n : ℕ,
            (∑ p ∈ pool.primes, FirstGaussPoolData.localErrorWeight p n *
              Q p ^ amplifierMovingExponent n) / pool.rowDensity M B ≤
                2 * idealCountConstant K * Z ^ eps := by
  obtain ⟨Zpit, hZpit, hpools⟩ :=
    exists_power_scale_exterior_pool A bad ell eps hell heps
  obtain ⟨Zdensity, hZdensity, hdensity⟩ :=
    uniform_pool_density_and_mass (A := A) ell eps Mmax Bmax
      hell heps hepsell hMmax hBmax
  refine ⟨max Zpit Zdensity, hZpit.trans_le (le_max_left _ _), ?_⟩
  intro Z hZ
  obtain ⟨pool⟩ := hpools Z ((le_max_left _ _).trans hZ)
  exact ⟨pool, hdensity Z ((le_max_right _ _).trans hZ) bad pool⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_uniform_original_pool
