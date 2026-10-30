import HeckeSkeleton.SmallRadius.FiniteUnitShellTest
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
Evaluate the actual finite unit-shell test for arbitrary additive Haar
measure. Its integral and negative-sign Fourier transform at zero equal
the actual positive mass of the shell. All norm-cpow weights disappear
pointwise because the original support has norm one.

The mass is retained as mu.real(shell); it is not normalized to one.
No Fourier--Mellin functional equation, multiplicative Haar comparison,
product-integral theorem or global additive probe is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellIntegralsDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open NumberField.StandardAddChar NumberField.AdelicFourier
open HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellTestDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem localUnitShell_measure_ne_zero : μ (localUnitShellSet K v) ≠ 0 := by
  apply (isClopen_localUnitShellSet K v).isOpen.measure_ne_zero μ
  exact ⟨1, (mem_localUnitShellSet_integer_iff K v 1).mpr isUnit_one⟩

theorem localUnitShell_measure_lt_top : μ (localUnitShellSet K v) < ⊤ :=
  (isCompact_localUnitShellSet K v).measure_lt_top

/-- Positive finite Haar mass of the actual shell, without a normalization. -/
theorem localUnitShell_measureReal_pos : 0 < μ.real (localUnitShellSet K v) :=
  ENNReal.toReal_pos (localUnitShell_measure_ne_zero K v μ)
    (localUnitShell_measure_lt_top K v μ).ne

theorem localUnitShellTest_integrable : Integrable (localUnitShellTest K v) μ :=
  (localUnitShellTest_locallyConstant K v).continuous.integrable_of_hasCompactSupport
    (localUnitShellTest_compactSupport K v)

theorem localUnitShellTest_integral :
    (∫ x : v.adicCompletion K, localUnitShellTest K v x ∂μ) =
      (μ.real (localUnitShellSet K v) : ℂ) := by
  change (∫ x : v.adicCompletion K,
    (localUnitShellSet K v).indicator (fun _ => (1 : ℂ)) x ∂μ) = _
  rw [integral_indicator_const (1 : ℂ)
    (isClopen_localUnitShellSet K v).isClosed.measurableSet]
  simp only [Complex.real_smul, mul_one]

theorem localUnitShellTest_integral_ne_zero :
    (∫ x : v.adicCompletion K, localUnitShellTest K v x ∂μ) ≠ 0 := by
  rw [localUnitShellTest_integral, Complex.ofReal_ne_zero]
  exact ne_of_gt (localUnitShell_measureReal_pos K v μ)

/-- Any actual additive character has the same Fourier value at zero. -/
theorem fourierIntegral_localUnitShellTest_zero
    (ψ : AddChar (v.adicCompletion K) ℂ) :
    fourierIntegral ψ μ (localUnitShellTest K v) 0 =
      (μ.real (localUnitShellSet K v) : ℂ) := by
  simp only [fourierIntegral, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  exact localUnitShellTest_integral K v μ

/-- The project's original standard local character and Fourier sign. -/
theorem fourierIntegral_psiLocal_localUnitShellTest_zero :
    fourierIntegral (psiLocal K v) μ (localUnitShellTest K v) 0 =
      (μ.real (localUnitShellSet K v) : ℂ) :=
  fourierIntegral_localUnitShellTest_zero K v μ (psiLocal K v)

theorem fourierIntegral_psiLocal_localUnitShellTest_zero_ne_zero :
    fourierIntegral (psiLocal K v) μ (localUnitShellTest K v) 0 ≠ 0 := by
  rw [fourierIntegral_psiLocal_localUnitShellTest_zero, Complex.ofReal_ne_zero]
  exact ne_of_gt (localUnitShell_measureReal_pos K v μ)

/-- This is a pointwise identity for the original function, including all
zero branches. It does not identify additive and multiplicative measures. -/
theorem localUnitShellTest_mul_norm_cpow (s : ℂ) (x : v.adicCompletion K) :
    localUnitShellTest K v x * (‖x‖ : ℂ) ^ s = localUnitShellTest K v x := by
  by_cases hx : localUnitShellTest K v x = 0
  · simp only [hx, zero_mul]
  · rw [localUnitShellTest_norm_eq_one K v hx, Complex.ofReal_one,
      Complex.one_cpow, mul_one]

theorem localUnitShellTest_weighted_integrable (s : ℂ) :
    Integrable (fun x : v.adicCompletion K =>
      localUnitShellTest K v x * (‖x‖ : ℂ) ^ s) μ := by
  have heq : (fun x : v.adicCompletion K =>
      localUnitShellTest K v x * (‖x‖ : ℂ) ^ s) = localUnitShellTest K v := by
    funext x
    exact localUnitShellTest_mul_norm_cpow K v s x
  rw [heq]
  exact localUnitShellTest_integrable K v μ

/-- Every complex norm exponent retains the exact same positive Haar mass. -/
theorem localUnitShellTest_weighted_integral (s : ℂ) :
    (∫ x : v.adicCompletion K,
      localUnitShellTest K v x * (‖x‖ : ℂ) ^ s ∂μ) =
      (μ.real (localUnitShellSet K v) : ℂ) := by
  simp_rw [localUnitShellTest_mul_norm_cpow]
  exact localUnitShellTest_integral K v μ

theorem localUnitShellTest_weighted_integral_ne_zero (s : ℂ) :
    (∫ x : v.adicCompletion K,
      localUnitShellTest K v x * (‖x‖ : ℂ) ^ s ∂μ) ≠ 0 := by
  rw [localUnitShellTest_weighted_integral, Complex.ofReal_ne_zero]
  exact ne_of_gt (localUnitShell_measureReal_pos K v μ)

section FiniteFactors

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μS : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μS p).IsAddHaarMeasure]

/-- The exact finite product of original local Fourier-zero factors.
This is a product of evaluated integrals, not an asserted product integral. -/
theorem finiteUnitShellFourierZero_product :
    (∏ p : S, fourierIntegral (psiLocal K p.val) (μS p)
      (localUnitShellTest K p.val) 0) =
      ∏ p : S, ((μS p).real (localUnitShellSet K p.val) : ℂ) := by
  apply Finset.prod_congr rfl
  intro p _hp
  exact fourierIntegral_psiLocal_localUnitShellTest_zero K p.val (μS p)

theorem finiteUnitShellFourierZero_product_ne_zero :
    (∏ p : S, fourierIntegral (psiLocal K p.val) (μS p)
      (localUnitShellTest K p.val) 0) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _hp
  exact fourierIntegral_psiLocal_localUnitShellTest_zero_ne_zero K p.val (μS p)

end FiniteFactors

end HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellIntegralsDraft
