module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3PoolData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform power density for one original prime pool

The two norm-exponent bounds precede the moving sources. A single
threshold absorbs the explicit row and frozen-divisor deletions and
the factor two, giving the exact power required by the S3 contract.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open NumberField IsDedekindDomain DedekindZetaZeroFree
open EngineStep EngineInduction.Source
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem exists_pool_with_power_density
    (A : SArithmeticData K) (bad : Finset (HeightOneSpectrum (𝓞 K)))
    (ell eps Mmax Bmax : ℝ) (hell : 0 < ell)
    (heps : 0 < eps) (hepsell : eps < ell) :
    ∃ threshold : ℝ, 1 < threshold ∧ ∀ Z : ℝ, threshold ≤ Z →
      ∃ pool : PowerScaleExteriorPool A bad Z ell eps,
        ∀ M B : ℝ, M ≤ Mmax → B ≤ Bmax →
          Z ^ (ell - 2 * eps) ≤ pool.rowDensity M B := by
  obtain ⟨Zpit, hZpit, hpools⟩ :=
    exists_power_scale_exterior_pool A bad ell eps hell heps
  have hlargeEvent := (_root_.tendsto_rpow_atTop (sub_pos.mpr hepsell)).eventually
    (Filter.eventually_ge_atTop (2 * (Mmax / (ell / 2) + Bmax / (ell / 2))))
  obtain ⟨Zlarge, hZlarge⟩ := Filter.eventually_atTop.mp hlargeEvent
  have hfactorEvent := (_root_.tendsto_rpow_atTop heps).eventually
    (Filter.eventually_ge_atTop (2 : ℝ))
  obtain ⟨Zfactor, hZfactor⟩ := Filter.eventually_atTop.mp hfactorEvent
  refine ⟨max Zpit (max Zlarge Zfactor), hZpit.trans_le (le_max_left _ _), ?_⟩
  intro Z hZ
  obtain ⟨pool⟩ := hpools Z ((le_max_left _ _).trans hZ)
  refine ⟨pool, ?_⟩
  intro M B hM hB
  have hZtail : max Zlarge Zfactor ≤ Z := (le_max_right _ _).trans hZ
  have hlarge : 2 * (M / (ell / 2) + B / (ell / 2)) ≤ Z ^ (ell - eps) := by
    apply le_trans _ (hZlarge Z ((le_max_left _ _).trans hZtail))
    exact mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right hM (by positivity))
        (div_le_div_of_nonneg_right hB (by positivity))) (by norm_num)
  have hfactor : 2 ≤ Z ^ eps := hZfactor Z ((le_max_right _ _).trans hZtail)
  have hZpos : 0 < Z := zero_lt_one.trans pool.base_gt_one
  have hpower : Z ^ (ell - 2 * eps) * Z ^ eps = Z ^ (ell - eps) := by
    rw [← Real.rpow_add hZpos]
    congr 1
    ring
  have hdouble : 2 * Z ^ (ell - 2 * eps) ≤ Z ^ (ell - eps) := by
    calc
      _ = Z ^ (ell - 2 * eps) * 2 := mul_comm _ _
      _ ≤ Z ^ (ell - 2 * eps) * Z ^ eps :=
        mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hZpos.le _)
      _ = _ := hpower
  exact (show Z ^ (ell - 2 * eps) ≤ Z ^ (ell - eps) / 2 by linarith).trans
    (pool.density_half M B hlarge)

theorem exists_source_pool_with_power_density
    (c : TargetContext K) (p : SourceParameters c) (Mmax Bmax : ℝ) :
    ∃ threshold : ℝ, 1 < threshold ∧ ∀ Z : ℝ, threshold ≤ Z →
      ∃ pool : PowerScaleExteriorPool (Arithmetic.data c) ∅ Z
          (recipeInductionSigma c / 3) p.loss,
        ∀ M B : ℝ, M ≤ Mmax → B ≤ Bmax →
          Z ^ (recipeInductionSigma c / 3 - 2 * p.loss) ≤ pool.rowDensity M B := by
  have hs := (recipeInduction_budget (c := c)).1
  exact exists_pool_with_power_density (Arithmetic.data c) ∅
    (recipeInductionSigma c / 3) p.loss Mmax Bmax (by positivity)
    p.loss_pos (by linarith [p.loss_small, p.loss_pos])

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.exists_pool_with_power_density
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.exists_source_pool_with_power_density
