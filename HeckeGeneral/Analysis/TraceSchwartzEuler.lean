import HeckeGeneral.Bridge.TraceSchwartzFourierBounds
import HeckeGeneral.Arithmetic.SLocalNormSection
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! The log-product-norm Euler operator on weighted trace Euclidean Schwartz
space. This proves Schwartz closure and derivatives of the actual dilation
curve, without asserting differentiation under an orbital integral. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Arithmetic
open scoped Classical NNReal

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "D" => (Module.finrank ℚ K : ℝ)

/-- Actual evaluation of the Schwartz differential against its position,
normalized by the field degree. It is continuous real linear. -/
def traceSchwartzEulerCLM : SchwartzMap V ℂ →L[ℝ] SchwartzMap V ℂ :=
  D⁻¹ • (SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply ℝ ℂ).flip
    (g := fun x : V => x) (by fun_prop)).comp (SchwartzMap.fderivCLM ℝ V ℂ)

@[simp] theorem traceSchwartzEulerCLM_apply (φ : SchwartzMap V ℂ) (x : V) :
    traceSchwartzEulerCLM K φ x = D⁻¹ • fderiv ℝ (φ : V → ℂ) x x := rfl

/-- This is exactly the positive norm section's infinite-place scale at eᵗ:
complex coordinates contribute twice to the product norm, already included in D. -/
theorem traceNormSection_exp_scale (t : ℝ) :
    (Real.exp t) ^ D⁻¹ = Real.exp (t / D) := by
  rw [div_eq_mul_inv, Real.exp_mul]

/-- Differentiating along actual log-norm dilation evaluates the Euler operator
at the dilated point. No nonzero condition on x is required. -/
theorem hasDerivAt_traceSchwartz_normDilation
    (φ : SchwartzMap V ℂ) (x : V) (t : ℝ) :
    HasDerivAt (fun u : ℝ => φ (Real.exp (u / D) • x))
      (traceSchwartzEulerCLM K φ (Real.exp (t / D) • x)) t := by
  have hg : HasDerivAt (fun u : ℝ => Real.exp (u / D) • x)
      (D⁻¹ • (Real.exp (t / D) • x)) t := by
    convert (((hasDerivAt_id t).div_const D).exp).smul_const x using 1 <;>
      simp [div_eq_mul_inv, smul_smul, mul_comm]
  have hh := (φ.hasFDerivAt (Real.exp (t / D) • x)).comp_hasDerivAt t hg
  simpa only [Function.comp_def, traceSchwartzEulerCLM_apply, map_smul] using hh

theorem deriv_traceSchwartz_normDilation
    (φ : SchwartzMap V ℂ) (x : V) (t : ℝ) :
    deriv (fun u : ℝ => φ (Real.exp (u / D) • x)) t =
      traceSchwartzEulerCLM K φ (Real.exp (t / D) • x) :=
  (hasDerivAt_traceSchwartz_normDilation K φ x t).deriv

/-- Every iterated Euler operator remains a genuine continuous linear operator. -/
def traceSchwartzEulerIterCLM : ℕ → SchwartzMap V ℂ →L[ℝ] SchwartzMap V ℂ
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (traceSchwartzEulerCLM K).comp (traceSchwartzEulerIterCLM j)

@[simp] theorem traceSchwartzEulerIterCLM_zero (φ : SchwartzMap V ℂ) :
    traceSchwartzEulerIterCLM K 0 φ = φ := rfl

@[simp] theorem traceSchwartzEulerIterCLM_succ (j : ℕ) (φ : SchwartzMap V ℂ) :
    traceSchwartzEulerIterCLM K (j + 1) φ =
      traceSchwartzEulerCLM K (traceSchwartzEulerIterCLM K j φ) := rfl

/-- A fixed iterated Euler seminorm is controlled by finitely many original
Schwartz seminorms. The indices and constant are selected before φ. -/
theorem traceSchwartzEulerIter_seminorm_bound (j k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ φ : SchwartzMap V ℂ,
        SchwartzMap.seminorm ℝ k n (traceSchwartzEulerIterCLM K j φ) ≤
          (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  let T := traceSchwartzEulerIterCLM K j
  let q : Seminorm ℝ (SchwartzMap V ℂ) :=
    (SchwartzMap.seminorm ℝ k n).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℝ V ℂ
  have hq : Continuous q := (hp.continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨s, C, hC, fun φ => ?_⟩
  have hφ := Seminorm.le_def.mp hb φ
  change SchwartzMap.seminorm ℝ k n (traceSchwartzEulerIterCLM K j φ) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ at hφ
  exact hφ

end HeckeGeneral.Analysis
