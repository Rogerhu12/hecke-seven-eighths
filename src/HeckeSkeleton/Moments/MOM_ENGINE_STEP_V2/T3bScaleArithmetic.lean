module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLengths
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FrozenScalarMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceScalarData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original scale arithmetic before packet realization

The ideal product length, the two original plain-divisor divisibilities
and the centered original scale bound are independent of the later
raw-family realization. They retain the original frozen ideals and
all four original plain scales.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem idealLogLength_mul (Z : ℝ) (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealLogLength Z (I * J) = idealLogLength Z I + idealLogLength Z J := by
  have hNI : (Ideal.absNorm I : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hNJ : (Ideal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  simp only [idealLogLength, map_mul, Nat.cast_mul, Real.log_mul hNI hNJ]
  ring

theorem plainDivisor_dvd_frozenSourceIdeal {k : ℕ}
    (D₁ D₂ : HeckeGeneral.Analysis.NonzeroIdeal K) (keep : Finset (Fin k))
    (primes : Fin k → HeightOneSpectrum (𝓞 K)) (plain : Bool) :
    (if plain then D₂ else D₁).val ∣ frozenSourceIdeal D₁ D₂ keep primes := by
  cases plain with
  | false => exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  | true => exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem allocated_plainDivisor_dvd_frozenIdeal {k : ℕ}
    (B : ActualColumnAllocation K k) (plain : Bool) :
    (B.plainDivisor (if plain then Fin.succ 0 else 0)).val ∣ B.frozenIdeal := by
  cases plain with
  | false => exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  | true => exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

theorem t3b_originalPlainScale_centered_lower (call : Call c)
    (hc : call.node.centered = true) (rectangle plain : Bool) :
    call.base ^ ((call.node.parameters.m + call.node.parameters.q) / 4) ≤
      call.originalPlainScale rectangle plain := by
  cases rectangle with
  | false =>
    cases plain with
    | false =>
      exact Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        (call.domain.centered_left hc)
    | true =>
      exact Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        (call.domain.centered_right hc)
  | true =>
    cases plain with
    | false =>
      change _ ≤ call.base ^ call.workingComparison₁
      rw [workingComparison₁, hc, if_pos rfl, call.domain.comparison_left hc]
    | true =>
      change _ ≤ call.base ^ call.workingComparison₂
      rw [workingComparison₂, hc, if_pos rfl, call.domain.comparison_right hc]
      apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
      have hl := call.domain.centered_left hc
      have hr := call.domain.centered_right hc
      linarith

end Call

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.idealLogLength_mul
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.plainDivisor_dvd_frozenSourceIdeal
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.allocated_plainDivisor_dvd_frozenIdeal
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.t3b_originalPlainScale_centered_lower
