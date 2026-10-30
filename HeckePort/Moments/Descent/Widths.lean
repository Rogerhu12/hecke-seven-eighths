import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Residual widths of a row

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Widths.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, in the form of its arithmetic core.

openai states these for the specific factorisation `I = rowPowerfulPart I * rowMaskPart I Q *
rowResidualPart I Q` of `GaussSum/PowerfulParts.lean` and for the specific reflection conductor
cost of `CubicSieve/NormalizedMass.lean` (neither is in the batch S0). Here the three factors are
an arbitrary factorisation `I = Pw * Mk * Rs` with `Mk ≠ ⊥`, and the reflection cost is an arbitrary
real number `cost` bounded by `N(Pw) N(Mk)^2 N(Q)` (the openai lemma
`reflectionConductorCost_bound`).  Norm identity used: `N(Rs) = N(I) / (N(Pw) N(Mk))`
(openai `rowResidualPart_norm`) is derived here from the factorisation.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

lemma actual_ideal_norm_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

/-- openai `actual_residual_norm_width`. -/
theorem actual_residual_norm_width (I Pw Mk Rs : Ideal (𝓞 K)) (hMk : Mk ≠ ⊥)
    (hprod : Pw * Mk * Rs = I) :
    (Ideal.absNorm Rs : ℝ) * (Ideal.absNorm Pw : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hm : 1 ≤ (Ideal.absNorm Mk : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hMk (Ideal.absNorm_eq_zero_iff.mp hz))
  have he := congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ)) hprod
  simp only [map_mul, Nat.cast_mul] at he
  calc
    _ ≤ (Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Mk : ℝ) * (Ideal.absNorm Rs : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (Ideal.absNorm Rs : ℝ) * (Ideal.absNorm Pw : ℝ) by positivity)
      nlinarith [hh]
    _ = _ := he

/-- openai `actual_common_width_charge`. -/
theorem actual_common_width_charge (I Pw Mk Rs Q : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hPw : Pw ≠ ⊥) (hMk : Mk ≠ ⊥) (hprod : Pw * Mk * Rs = I) (cost : ℝ)
    (hcost : cost ≤ (Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Mk : ℝ) ^ 2 *
      (Ideal.absNorm Q : ℝ)) :
    (Ideal.absNorm Rs : ℝ) ^ 2 * cost ≤
      (Ideal.absNorm I : ℝ) ^ 2 / (Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Q : ℝ) := by
  have hp := actual_ideal_norm_pos Pw hPw
  have hm := actual_ideal_norm_pos Mk hMk
  have he := congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ)) hprod
  simp only [map_mul, Nat.cast_mul] at he
  have hr : (Ideal.absNorm Rs : ℝ) =
      (Ideal.absNorm I : ℝ) / ((Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Mk : ℝ)) := by
    rw [eq_div_iff (mul_pos hp hm).ne', ← he]
    ring
  calc
    _ ≤ (Ideal.absNorm Rs : ℝ) ^ 2 *
        ((Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Mk : ℝ) ^ 2 * (Ideal.absNorm Q : ℝ)) :=
      mul_le_mul_of_nonneg_left hcost (sq_nonneg _)
    _ = _ := by rw [hr]; field_simp

/-- openai `actual_common_width_charge_label_puncture`. -/
theorem actual_common_width_charge_label_puncture
    (I F rho S Pw Mk Rs : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hF : F ≠ ⊥) (hrho : rho ≠ ⊥)
    (hS : S ≠ ⊥) (hPw : Pw ≠ ⊥) (hMk : Mk ≠ ⊥) (hprod : Pw * Mk * Rs = I) (cost : ℝ)
    (hcost : cost ≤ (Ideal.absNorm Pw : ℝ) * (Ideal.absNorm Mk : ℝ) ^ 2 *
      (Ideal.absNorm (S * F * rho) : ℝ)) :
    (Ideal.absNorm Rs : ℝ) ^ 2 * cost ≤
      (Ideal.absNorm S : ℝ) *
        ((Ideal.absNorm I : ℝ) ^ 2 / (Ideal.absNorm Pw : ℝ)) *
        (Ideal.absNorm F : ℝ) * (Ideal.absNorm rho : ℝ) := by
  have _ := hF
  have _ := hrho
  have _ := hS
  convert actual_common_width_charge I Pw Mk Rs (S * F * rho) hI hPw hMk hprod cost hcost using 1
  simp only [map_mul, Nat.cast_mul]
  ring

end HeckePort.Moments

end
