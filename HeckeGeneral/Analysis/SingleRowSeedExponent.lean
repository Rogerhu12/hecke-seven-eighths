import HeckeGeneral.Analysis.EndpointClosure
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!

Pure inequality consumption of a normalized SINGLE-ROW energy estimate.
This estimate is not renamed as the independent two-scale input I.
Deriving it from MI, ideal counting, the exact sixth-power-mask average,
and the required canonical-row normalization remains an open obligation.

The conclusion concerns the actual complex-valued amplified function
sqrt(D) * M(D), rather than only a numerical comparison of exponents.
No seed zero bound, Mellin continuation, or zero-free theorem is asserted.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments
open Filter Asymptotics
open scoped Topology

/-- The normalized single-row estimate with all small positive losses.
The constant is chosen after c and epsilon and before the scale D. -/
def NormalizedSingleRowEnergy (M : ℝ → ℂ) : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D →
      ‖M D‖ ^ 2 ≤ C * D ^ (5 * (1 + c) / 6 + ε)

/-- Pointwise square-bound consumption, with the square-root amplification
and exponent doubling made explicit. -/
theorem norm_sqrt_mul_le_rpow_of_energy_bound
    {D C a β : ℝ} (z : ℂ) (hD : 1 ≤ D) (hC : 0 ≤ C)
    (henergy : ‖z‖ ^ 2 ≤ C * D ^ a)
    (hexponent : 1 / 2 + a / 2 ≤ β) :
    ‖(Real.sqrt D : ℂ) * z‖ ≤ Real.sqrt C * D ^ β := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hexponent' : 1 + a ≤ 2 * β := by linarith
  have hsq : ‖(Real.sqrt D : ℂ) * z‖ ^ 2 ≤ C * D ^ (2 * β) := by
    calc
      _ = D * ‖z‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg D),
          mul_pow, Real.sq_sqrt hD0]
      _ ≤ D * (C * D ^ a) := mul_le_mul_of_nonneg_left henergy hD0
      _ = C * D ^ (1 + a) := by
        rw [Real.rpow_add hDpos, Real.rpow_one]
        ring
      _ ≤ C * D ^ (2 * β) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hD hexponent') hC
  have htargetsq : (Real.sqrt C * D ^ β) ^ 2 = C * D ^ (2 * β) := by
    rw [mul_pow, Real.sq_sqrt hC, ← Real.rpow_mul_natCast hD0 β 2]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg C) (Real.rpow_nonneg hD0 β))).mp
  rw [htargetsq]
  exact hsq

/-- The existing strict exponent margin now yields a bound for the
amplified complex-valued single row at every D >= 1. -/
theorem singleRowEnergy_amplification_pointwise (M : ℝ → ℂ)
    (henergy : NormalizedSingleRowEnergy M) {β : ℝ} (hβ : 11 / 12 < β) :
    ∃ B : ℝ, 0 < B ∧ ∀ D : ℝ, 1 ≤ D →
      ‖(Real.sqrt D : ℂ) * M D‖ ≤ B * D ^ β := by
  obtain ⟨c, ε, hc, hε, hmargin⟩ := seed_amplification_exponent_margin hβ
  obtain ⟨C, hC, hbound⟩ := henergy c ε hc hε
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, ?_⟩
  intro D hD
  exact norm_sqrt_mul_le_rpow_of_energy_bound (M D) hD hC.le
    (hbound D hD) hmargin.le

/-- For every beta > 11/12, the genuine square-root-amplified function
has the claimed power growth at infinity. This consumes the single-row
energy hypothesis; it does not derive that hypothesis from MI. -/
theorem singleRowEnergy_amplification_isBigO (M : ℝ → ℂ)
    (henergy : NormalizedSingleRowEnergy M) {β : ℝ} (hβ : 11 / 12 < β) :
    (fun D : ℝ => (Real.sqrt D : ℂ) * M D) =O[atTop] (fun D : ℝ => D ^ β) := by
  obtain ⟨B, _hB, hbound⟩ := singleRowEnergy_amplification_pointwise M henergy hβ
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨B, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hD) β)]
  exact hbound D hD

end HeckeGeneral.Analysis.ConditionalMoments
