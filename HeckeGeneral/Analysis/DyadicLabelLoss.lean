import HeckeGeneral.Analysis.TInputUniformMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A fixed power of log Z active labels costs arbitrarily small scale
power. This lemma does not assert that a particular detector decomposition
has that many labels; its actual dyadic enumeration must supply the count. -/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open Filter Asymptotics
open scoped Topology

theorem polynomialLogLabelCount_subpower {ι : Type} (active : ℝ → Finset ι)
    (k : ℕ)
    (hlabels : ∃ L Z₀ : ℝ, 0 < L ∧ 1 ≤ Z₀ ∧
      ∀ Z, Z₀ ≤ Z → ((active Z).card : ℝ) ≤ L * (1 + Real.log Z) ^ k)
    {η : ℝ} (hη : 0 < η) :
    ∃ C Z₁ : ℝ, 0 < C ∧ 1 ≤ Z₁ ∧
      ∀ Z, Z₁ ≤ Z → ((active Z).card : ℝ) ≤ C * Z ^ η := by
  obtain ⟨L, Z₀, hL, hZ₀, hb⟩ := hlabels
  have hlog := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hη).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Z₂, hZ₂⟩ := eventually_atTop.mp hlog
  refine ⟨L * 2 ^ k, max Z₀ (max Z₂ (Real.exp 1)),
    mul_pos hL (by positivity), hZ₀.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hbase : Z₀ ≤ Z := (le_max_left _ _).trans hZ
  have hlarge : Z₂ ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hexp : Real.exp 1 ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.exp_pos 1) hexp
  have hlog1 : 1 ≤ Real.log Z := (Real.le_log_iff_exp_le hZpos).mpr hexp
  have ht := hZ₂ Z hlarge
  simp only [Real.rpow_natCast,
    Real.norm_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log Z) k),
    Real.norm_of_nonneg (Real.rpow_nonneg hZpos.le _), one_mul] at ht
  calc
    _ ≤ L * (1 + Real.log Z) ^ k := hb Z hbase
    _ ≤ L * (2 * Real.log Z) ^ k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) k) hL.le
    _ = (L * 2 ^ k) * (Real.log Z) ^ k := by rw [mul_pow]; ring
    _ ≤ (L * 2 ^ k) * Z ^ η := mul_le_mul_of_nonneg_left ht (by positivity)

end HeckeGeneral.Analysis.ConditionalMoments
