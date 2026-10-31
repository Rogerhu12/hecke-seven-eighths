import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolGaussDecomposition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedCommonMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The single pool density pays the complete prime-label mass

The upper cardinal bound is derived from ordinary ideal counting on the
actual exterior prime carrier. The lower density is the earlier PIT
power bound minus the explicit row and frozen-ideal deletion terms.
The scale threshold is chosen before those moving ideals and rows.

The exact squared factors at depths 1 and 7 cancel their actual moving
prime norm. The depth-6 factor is at most one. Thus summing the errors
over the original one pool costs only its one density and a small power,
not a second amplification or an assumed aggregate prime count.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

namespace PowerScaleExteriorPool

theorem card_upper (P : PowerScaleExteriorPool A bad Z ell eps) :
    (P.primes.card : ℝ) ≤ idealCountConstant K * Z ^ ell := by
  let ideals := P.primes.image (fun p => p.val.asIdeal)
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) := by
    intro p q he
    exact Subtype.ext (HeightOneSpectrum.asIdeal_injective he)
  have hc : ideals.card = P.primes.card := Finset.card_image_of_injective _ hinj
  have hN : ∀ I ∈ ideals, (Ideal.absNorm I : ℝ) ≤ Z ^ ell := by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact P.norm_upper p hp
  have h := card_le_idealCountConstant K ideals (Z ^ ell)
    (Real.one_le_rpow P.base_gt_one.le P.exponent_pos.le) hN
  rwa [hc] at h

theorem density_half (P : PowerScaleExteriorPool A bad Z ell eps)
    (M B : ℝ) (hlarge : 2 * (M / (ell / 2) + B / (ell / 2)) ≤ Z ^ (ell - eps)) :
    Z ^ (ell - eps) / 2 ≤ P.rowDensity M B := by
  unfold rowDensity
  linarith

theorem density_inverse (P : PowerScaleExteriorPool A bad Z ell eps)
    (M B : ℝ) (hlarge : 2 * (M / (ell / 2) + B / (ell / 2)) ≤ Z ^ (ell - eps)) :
    1 / P.rowDensity M B ≤ 2 * Z ^ (-ell + eps) := by
  have hz := zero_lt_one.trans P.base_gt_one
  have hp : 0 < Z ^ (ell - eps) / 2 := by positivity
  apply (one_div_le_one_div_of_le hp (P.density_half M B hlarge)).trans_eq
  rw [show -ell + eps = -(ell - eps) by ring, Real.rpow_neg hz.le]
  ring

theorem card_div_density (P : PowerScaleExteriorPool A bad Z ell eps)
    (M B : ℝ) (hlarge : 2 * (M / (ell / 2) + B / (ell / 2)) ≤ Z ^ (ell - eps)) :
    (P.primes.card : ℝ) / P.rowDensity M B ≤ 2 * idealCountConstant K * Z ^ eps := by
  have hz := zero_lt_one.trans P.base_gt_one
  have hd : 0 < P.rowDensity M B :=
    lt_of_lt_of_le (by positivity) (P.density_half M B hlarge)
  calc
    _ = (P.primes.card : ℝ) * (1 / P.rowDensity M B) := by ring
    _ ≤ (idealCountConstant K * Z ^ ell) * (2 * Z ^ (-ell + eps)) :=
      mul_le_mul P.card_upper (P.density_inverse M B hlarge)
        (one_div_nonneg.mpr hd.le)
        (mul_nonneg (zero_le_one.trans (one_le_idealCountConstant K))
          (Real.rpow_nonneg hz.le _))
    _ = 2 * idealCountConstant K * Z ^ eps := by
      rw [show (idealCountConstant K * Z ^ ell) * (2 * Z ^ (-ell + eps)) =
        (2 * idealCountConstant K) * (Z ^ ell * Z ^ (-ell + eps)) by ring,
        ← Real.rpow_add hz]
      congr 2
      ring

end PowerScaleExteriorPool

/-- The moving radical exponent removed by an actual amplifier error. -/
def amplifierMovingExponent (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 7 then 1 else 0

theorem localErrorWeight_mul_moving_norm_le_one (p : ExteriorPrime A) (n : ℕ) :
    FirstGaussPoolData.localErrorWeight p n * Q p ^ amplifierMovingExponent n ≤ 1 := by
  have hQ : 1 ≤ Q p := by
    change (1 : ℝ) ≤ (Ideal.absNorm p.val.asIdeal : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun he => p.val.ne_bot (Ideal.absNorm_eq_zero_iff.mp he))
  have hp : 0 < Q p := zero_lt_one.trans_le hQ
  have hi0 : 0 ≤ (Q p)⁻¹ := inv_nonneg.mpr hp.le
  have hi1 : (Q p)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hQ
  by_cases h1 : n = 1
  · subst n
    simp [FirstGaussPoolData.localErrorWeight, amplifierMovingExponent, hp.ne']
  by_cases h6 : n = 6
  · subst n
    norm_num [FirstGaussPoolData.localErrorWeight, amplifierMovingExponent]
    nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hi1)]
  by_cases h7 : n = 7
  · subst n
    simp [FirstGaussPoolData.localErrorWeight, amplifierMovingExponent, hp.ne']
  · simp only [FirstGaussPoolData.localErrorWeight, amplifierMovingExponent,
      h1, h6, h7, if_false, zero_mul, zero_le_one]

/-- Exact local moving-support payments followed by one pool density. -/
theorem actual_error_pool_mass (P : PowerScaleExteriorPool A bad Z ell eps)
    (M B : ℝ) (hlarge : 2 * (M / (ell / 2) + B / (ell / 2)) ≤ Z ^ (ell - eps))
    (n : ℕ) :
    (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p n *
      Q p ^ amplifierMovingExponent n) / P.rowDensity M B ≤
        2 * idealCountConstant K * Z ^ eps := by
  have hd : 0 < P.rowDensity M B := lt_of_lt_of_le
    (by have := P.base_gt_one; positivity) (P.density_half M B hlarge)
  have hs : (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p n *
      Q p ^ amplifierMovingExponent n) ≤ (P.primes.card : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ P.primes, (1 : ℝ) :=
        Finset.sum_le_sum (fun p _ => localErrorWeight_mul_moving_norm_le_one p n)
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hs hd.le).trans (P.card_div_density M B hlarge)

/-- One threshold works for every pool, row norm, frozen ideal and
internal divisor within the fixed norm-exponent box. -/
theorem uniform_pool_density_and_mass (ell eps Mmax Bmax : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hM : 0 ≤ Mmax) (hB : 0 ≤ Bmax) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ P : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, M ≤ Mmax → B ≤ Bmax →
      0 < P.rowDensity M B ∧
      1 / P.rowDensity M B ≤ 2 * Z ^ (-ell + eps) ∧
      (P.primes.card : ℝ) / P.rowDensity M B ≤ 2 * idealCountConstant K * Z ^ eps ∧
      ∀ n : ℕ,
        (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p n *
          Q p ^ amplifierMovingExponent n) / P.rowDensity M B ≤
            2 * idealCountConstant K * Z ^ eps := by
  have hexp : 0 < ell - eps := sub_pos.mpr hepsell
  have hevent := (_root_.tendsto_rpow_atTop hexp).eventually
    (Filter.eventually_ge_atTop (2 * (Mmax / (ell / 2) + Bmax / (ell / 2))))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ bad P M B hMM hBB
  have hlarge : 2 * (M / (ell / 2) + B / (ell / 2)) ≤ Z ^ (ell - eps) := by
    apply le_trans _ (hZ₁ Z ((le_max_left _ _).trans hZ))
    exact mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right hMM (by positivity))
        (div_le_div_of_nonneg_right hBB (by positivity))) (by norm_num)
  have hd : 0 < P.rowDensity M B := lt_of_lt_of_le
    (by have := P.base_gt_one; positivity) (P.density_half M B hlarge)
  exact ⟨hd, P.density_inverse M B hlarge, P.card_div_density M B hlarge,
    fun n => actual_error_pool_mass P M B hlarge n⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_error_pool_mass
#print axioms HeckeSkeleton.Moments.EngineStep.uniform_pool_density_and_mass
