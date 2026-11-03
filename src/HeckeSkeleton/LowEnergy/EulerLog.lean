import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Euler derivatives in logarithmic coordinates

`euler` and `eulerOrder` are definitionally the operations in the supplied
`GlobalThetaData`.  They are repeated here solely to keep this analytic lemma
independent of the project's unavailable arithmetic dependency closure.
The integral uses the exact two weights of the project's `testIntegral`.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.EulerLog

open MeasureTheory Set Filter
open scoped ContDiff Topology

def euler (f : ℝ → ℂ) : ℝ → ℂ := fun y => (y : ℂ) * deriv f y

def eulerOrder (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ := (euler^[j]) f

theorem eulerOrder_succ (j : ℕ) (f : ℝ → ℂ) :
    eulerOrder (j + 1) f = euler (eulerOrder j f) := by
  simp only [eulerOrder, Function.iterate_succ_apply']

/-- An identity on the positive half-line suffices; no regularity at zero is used. -/
theorem eulerOrder_log (F f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ y : ℝ, 0 < y → F y = f (Real.log y))
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    eulerOrder j F x = iteratedDeriv j f (Real.log x) := by
  induction j generalizing x with
  | zero => simpa [eulerOrder] using hF x hx
  | succ j ih =>
    have heq : eulerOrder j F =ᶠ[𝓝 x]
        (fun y => iteratedDeriv j f (Real.log y)) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih hy
    have hd := (((contDiff_iff_iteratedDeriv.mp hf).2 j
      (ENat.natCast_lt_top j)) (Real.log x)).hasDerivAt
    have hc := hd.scomp x (Real.hasDerivAt_log hx.ne')
    have hc' := hc.deriv
    simp only [Function.comp_def] at hc'
    rw [eulerOrder_succ, euler, heq.deriv_eq, hc']
    rw [iteratedDeriv_succ]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.ne'), one_mul]

theorem iteratedDeriv_ofReal (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    iteratedDeriv j (fun x => (f x : ℂ)) = fun x => ((iteratedDeriv j f x : ℝ) : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
    funext x
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      (((contDiff_iff_iteratedDeriv.mp hf).2 j (ENat.natCast_lt_top j)) x).hasDerivAt).deriv

/-- The actual two-weight test integral becomes a compact logarithmic integral. -/
theorem testIntegral_log (F f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ y : ℝ, 0 < y → F y = f (Real.log y)) (j : ℕ) (A : ℝ) :
    (∫ y in Ioi (0 : ℝ), ‖eulerOrder j F y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y) =
    ∫ u : ℝ, ‖iteratedDeriv j f u‖ *
      (Real.exp (u / 4) + Real.exp (-A * u)) := by
  rw [← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [eulerOrder_log F f hf hF j (Real.exp_pos _), Real.log_exp]
  simp only [smul_eq_mul, ← Real.exp_mul]
  have he := Real.exp_ne_zero u
  field_simp [he]

theorem integrable_testIntegral_iff (F f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ y : ℝ, 0 < y → F y = f (Real.log y)) (j : ℕ) (A : ℝ) :
    IntegrableOn (fun y : ℝ => ‖eulerOrder j F y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y) (Ioi 0) ↔
    Integrable (fun u : ℝ => ‖iteratedDeriv j f u‖ *
      (Real.exp (u / 4) + Real.exp (-A * u))) := by
  rw [← integrable_comp_exp]
  apply integrable_congr
  filter_upwards [] with u
  rw [eulerOrder_log F f hf hF j (Real.exp_pos _), Real.log_exp]
  simp only [smul_eq_mul, ← Real.exp_mul]
  have he := Real.exp_ne_zero u
  field_simp [he]

#print axioms eulerOrder_log
#print axioms iteratedDeriv_ofReal
#print axioms testIntegral_log

end HeckeSkeleton.LowEnergy.EulerLog
