module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EstimateData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original profile point bounds and one fixed frozen-atom budget

These bounds use only the original profile input and the selected
source tilt. They do not require an ordinary or exceptional child.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem power_annulus_bound (x lower power : ℝ)
    (hlower : 0 < lower) (hx : lower ≤ x) (hp : -1 ≤ power) (hp' : power ≤ 0) :
    x ^ power ≤ max 1 lower⁻¹ := by
  have hxpos : 0 < x := hlower.trans_le hx
  by_cases hlog : 0 ≤ Real.log x
  · have hproduct : Real.log x * power ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlog hp'
    calc
      x ^ power = Real.exp (Real.log x * power) := Real.rpow_def_of_pos hxpos _
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hproduct
      _ = 1 := Real.exp_zero
      _ ≤ max 1 lower⁻¹ := le_max_left _ _
  · have hproduct : Real.log x * power ≤ Real.log x * (-1) :=
      mul_le_mul_of_nonpos_left hp (lt_of_not_ge hlog).le
    have hpow : x ^ power ≤ x ^ (-1 : ℝ) := by
      rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hxpos]
      exact Real.exp_le_exp.mpr hproduct
    calc
      x ^ power ≤ x⁻¹ := by simpa only [Real.rpow_neg_one] using hpow
      _ ≤ lower⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hlower hx
      _ ≤ max 1 lower⁻¹ := le_max_right _ _

namespace ProfileInput

variable (input : ProfileInput call)

def frozenAmplitude : ℝ :=
  input.amplitude * max 1 (call.prepared.lower / 2)⁻¹

theorem frozenAmplitude_nonneg : 0 ≤ input.frozenAmplitude :=
  mul_nonneg (zero_le_one.trans input.amplitude_one_le)
    (zero_le_one.trans (le_max_left _ _))

theorem original_prime_norm_le (horders : (0, 0) ∈ input.orders)
    (i : Fin call.node.data.geometry.slotCount) (x : ℝ) :
    ‖(call.node.data.geometry.slots i).profile 0 x‖ ≤ input.amplitude := by
  rw [input.raw.prime_eq]
  have h := OriginalProfileAtomBounds.norm_le_profileOrders input.orders
    (input.raw.primeRep i 0) x
  rw [OriginalProfileAtomBounds.profileOrders, Finset.insert_eq_of_mem horders] at h
  exact h.trans (input.raw.prime_bound i 0 (Set.mem_univ _))

theorem tilted_prime_norm_le (horders : (0, 0) ∈ input.orders)
    (i : Fin call.node.data.geometry.slotCount) (x : ℝ) (hx : x ∈ call.window) :
    ‖(call.node.data.geometry.slots i).profile 0 x *
      ((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ)‖ ≤ input.frozenAmplitude := by
  have hxpos := call.window_positive hx
  have hpower : x ^ (-1 + 2 * p.tilt) ≤ max 1 (call.prepared.lower / 2)⁻¹ :=
    power_annulus_bound x (call.prepared.lower / 2) (-1 + 2 * p.tilt)
      (div_pos call.prepared.lower_pos (by norm_num)) hx.1
      (by linarith [p.tilt_pos]) (by linarith [p.tilt_half])
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hxpos _)]
  exact mul_le_mul (input.original_prime_norm_le horders i x) hpower
    (Real.rpow_nonneg hxpos.le _) (zero_le_one.trans input.amplitude_one_le)

def frozenAtomBudget : ℝ :=
  max 1 (2 * call.prepared.upper * input.frozenAmplitude ^ 2)

theorem frozenAtomBudget_one : 1 ≤ input.frozenAtomBudget := le_max_left _ _

end ProfileInput

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileInput.original_prime_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileInput.tilted_prime_norm_le
