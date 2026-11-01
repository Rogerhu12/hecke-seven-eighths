import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorBlockTerminal

/-!
# Combine the original first weight with the actual second coefficients

The first row profile does not contain the negative central degree of
the original columns. That degree stays in the actual second Gram
coefficients. The two powers are combined here before a uniform source
constant is claimed. The original first allowances, first divisor,
Fourier mass, and both actual source fibres are unchanged.

The stage lemmas consume only the amplitude fields of an already
constructed dual calibration and its original tuple and fibre counts.
They do not require the obsolete all-column lower window or a bound on
the finished terminal. Both the supported zero product and the full
Cartesian tail product remain those of the same calibration.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open MeasureTheory

/-- The scale in the actual first row weight cancels the opposite
scale supplied by the original column coefficients, before summing
the two source sides. The first divisor is still paid exactly once. -/
theorem original_terminal_class_scalar_with_shift
    (Z parentWidth NL NR row mob phase mass massBound left right CL CR
      divisorNorm loss shift amplitude commonWeight : ℝ)
    (hZ : 0 < Z) (hNL : 0 < NL) (hNR : 0 < NR)
    (hrow : 0 ≤ row) (hmob : 0 ≤ mob) (hphase : 0 ≤ phase)
    (hmass : 0 ≤ mass) (hmassBound : 0 ≤ massBound)
    (hCL : 0 ≤ CL) (hCR : 0 ≤ CR) (hdivisor : 0 ≤ divisorNorm)
    (hleft : left / NL ≤ (CL / divisorNorm) * Z ^ (loss - shift))
    (hright : right / NR ≤ (CR / divisorNorm) * Z ^ (loss - shift))
    (hFourier : mass ≤ massBound)
    (hfirst : row * Real.sqrt NL * Real.sqrt NR / Z ^ parentWidth ≤
      (amplitude * Z ^ shift) * commonWeight) :
    (mob * phase * (row * Real.sqrt NL * Real.sqrt NR / 2) *
        (mass * left / NL + mass * right / NR)) / Z ^ parentWidth ≤
      (amplitude * massBound * ((CL + CR) / 2)) *
        (commonWeight * (mob / divisorNorm) * phase) * Z ^ loss := by
  have h := original_terminal_class_scalar Z parentWidth NL NR row mob phase mass massBound
    left right CL CR divisorNorm (loss - shift) (amplitude * Z ^ shift) commonWeight
    hZ hNL hNR hrow hmob hphase hmass hmassBound hCL hCR hdivisor
    hleft hright hFourier hfirst
  apply h.trans_eq
  calc
    _ = ((amplitude * massBound * ((CL + CR) / 2)) *
        (commonWeight * (mob / divisorNorm) * phase)) *
          (Z ^ shift * Z ^ (loss - shift)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ]
      congr 2
      ring

/-- This is the exact algebraic movement of the original central
degree. No estimate on the first profile without that degree is used. -/
theorem first_profile_power_with_shift
    (Z parentWidth total shift amplitude profile : ℝ) (hZ : 0 < Z)
    (hprofile : profile ≤ amplitude * Z ^ (parentWidth - total + shift)) :
    profile ≤ (amplitude * Z ^ shift) * Z ^ (parentWidth - total) := by
  apply hprofile.trans_eq
  rw [Real.rpow_add hZ]
  ring

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualGaussStage.DualTerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}
variable (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)

private theorem coefficient_le_of_counts
    (Cterminal profile divisorNorm : ℝ) (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Cterminal) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hfiber : s.fiber ≤ fiberCap) (htuples : T.windows.multiplicity ≤ tupleCap) :
    (s.fiber : ℝ) * Cterminal * T.windows.multiplicity * (profile / divisorNorm) ≤
      ((fiberCap : ℝ) * Cterminal * (tupleCap : ℝ) * profile) / divisorNorm := by
  have hf : (s.fiber : ℝ) ≤ (fiberCap : ℝ) := by exact_mod_cast hfiber
  have ht : (T.windows.multiplicity : ℝ) ≤ (tupleCap : ℝ) := by exact_mod_cast htuples
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul hf ht (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (mul_nonneg hC (div_nonneg hprofile hdivisor))
  convert h using 1 <;> ring

/-- The supported-zero amplitude already contains the central decay
and the original divisor payment. This lemma retains both through the
literal original first allowance. -/
theorem zeroBudget_div_allowance_le_of_amplitude
    (ε Czero profile divisorNorm amplitudeExponent allowance loss shift : ℝ)
    (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hfiber : s.fiber ≤ fiberCap) (htuples : T.windows.multiplicity ≤ tupleCap)
    (hAmplitude : T.zeroAmplitude ≤ (profile / divisorNorm) * Z ^ amplitudeExponent)
    (hbudget : amplitudeExponent + T.zeroProductExponent * ε ≤ allowance + loss - shift) :
    T.zeroBudget ε Czero / Z ^ allowance ≤
      (((fiberCap : ℝ) * Czero * (tupleCap : ℝ) * profile) / divisorNorm) *
        Z ^ (loss - shift) := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hpart := T.zeroBudget_le_power ε Czero (profile / divisorNorm)
    amplitudeExponent (allowance + loss - shift) hC (div_nonneg hprofile hdivisor)
    hAmplitude hbudget
  have hcounts := T.coefficient_le_of_counts Czero profile divisorNorm fiberCap tupleCap
    hC hprofile hdivisor hfiber htuples
  have hfull := hpart.trans (mul_le_mul_of_nonneg_right hcounts
    (Real.rpow_nonneg hz.le (allowance + loss - shift)))
  apply (div_le_div_of_nonneg_right hfull (Real.rpow_nonneg hz.le allowance)).trans_eq
  rw [mul_div_assoc, ← Real.rpow_sub hz]
  congr 2
  ring

/-- The full-Cartesian tail uses the same first divisor and allowance.
Its cutoff saving is combined with the original central degree before
the first profile is estimated. -/
theorem tailBudget_div_allowance_le_of_amplitude
    (Cerror profile divisorNorm amplitudeExponent allowance loss shift : ℝ)
    (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hfiber : s.fiber ≤ fiberCap) (htuples : T.windows.multiplicity ≤ tupleCap)
    (hAmplitude : T.tailAmplitude ≤ (profile / divisorNorm) * Z ^ amplitudeExponent)
    (hbudget : amplitudeExponent - Nsave ≤ allowance + loss - shift) :
    T.tailBudget Cerror / Z ^ allowance ≤
      (((fiberCap : ℝ) * Cerror * (tupleCap : ℝ) * profile) / divisorNorm) *
        Z ^ (loss - shift) := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hpart := T.tailBudget_le_power Cerror (profile / divisorNorm)
    amplitudeExponent (allowance + loss - shift) hC (div_nonneg hprofile hdivisor)
    hAmplitude hbudget
  have hcounts := T.coefficient_le_of_counts Cerror profile divisorNorm fiberCap tupleCap
    hC hprofile hdivisor hfiber htuples
  have hfull := hpart.trans (mul_le_mul_of_nonneg_right hcounts
    (Real.rpow_nonneg hz.le (allowance + loss - shift)))
  apply (div_le_div_of_nonneg_right hfull (Real.rpow_nonneg hz.le allowance)).trans_eq
  rw [mul_div_assoc, ← Real.rpow_sub hz]
  congr 2
  ring

/-- An empty actual row fibre costs zero. The divisor and sharp
window estimates are therefore needed only on the original nonzero
fibre, where the actual source supplies their divisibility gate. -/
theorem zeroBudget_div_allowance_le_of_nonzero_fiber
    (ε Czero profile divisorNorm amplitudeExponent allowance loss shift : ℝ)
    (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hfiber : s.fiber ≤ fiberCap) (htuples : T.windows.multiplicity ≤ tupleCap)
    (hAmplitude : s.fiber ≠ 0 →
      T.zeroAmplitude ≤ (profile / divisorNorm) * Z ^ amplitudeExponent)
    (hbudget : s.fiber ≠ 0 →
      amplitudeExponent + T.zeroProductExponent * ε ≤ allowance + loss - shift) :
    T.zeroBudget ε Czero / Z ^ allowance ≤
      (((fiberCap : ℝ) * Czero * (tupleCap : ℝ) * profile) / divisorNorm) *
        Z ^ (loss - shift) := by
  by_cases hf : s.fiber = 0
  · have hz : 0 ≤ Z := zero_le_one.trans T.windows.base_ge_one
    simp only [zeroBudget, hf, Nat.cast_zero, zero_mul, zero_div]
    exact mul_nonneg (div_nonneg (by positivity) hdivisor) (Real.rpow_nonneg hz _)
  · exact T.zeroBudget_div_allowance_le_of_amplitude ε Czero profile divisorNorm
      amplitudeExponent allowance loss shift fiberCap tupleCap hC hprofile hdivisor
      hfiber htuples (hAmplitude hf) (hbudget hf)

/-- The full-Cartesian tail uses the same empty-fibre convention and
does not impose a false post-pool divisor gate on an empty source. -/
theorem tailBudget_div_allowance_le_of_nonzero_fiber
    (Cerror profile divisorNorm amplitudeExponent allowance loss shift : ℝ)
    (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hfiber : s.fiber ≤ fiberCap) (htuples : T.windows.multiplicity ≤ tupleCap)
    (hAmplitude : s.fiber ≠ 0 →
      T.tailAmplitude ≤ (profile / divisorNorm) * Z ^ amplitudeExponent)
    (hbudget : s.fiber ≠ 0 →
      amplitudeExponent - Nsave ≤ allowance + loss - shift) :
    T.tailBudget Cerror / Z ^ allowance ≤
      (((fiberCap : ℝ) * Cerror * (tupleCap : ℝ) * profile) / divisorNorm) *
        Z ^ (loss - shift) := by
  by_cases hf : s.fiber = 0
  · have hz : 0 ≤ Z := zero_le_one.trans T.windows.base_ge_one
    simp only [tailBudget, hf, Nat.cast_zero, zero_mul, zero_div]
    exact mul_nonneg (div_nonneg (by positivity) hdivisor) (Real.rpow_nonneg hz _)
  · exact T.tailBudget_div_allowance_le_of_amplitude Cerror profile divisorNorm
      amplitudeExponent allowance loss shift fiberCap tupleCap hC hprofile hdivisor
      hfiber htuples (hAmplitude hf) (hbudget hf)

end ActualGaussStage.DualTerminalCalibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_terminal_class_scalar_with_shift
#print axioms HeckeSkeleton.Moments.EngineStep.first_profile_power_with_shift
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.zeroBudget_div_allowance_le_of_amplitude
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.tailBudget_div_allowance_le_of_amplitude
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.zeroBudget_div_allowance_le_of_nonzero_fiber
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.tailBudget_div_allowance_le_of_nonzero_fiber
