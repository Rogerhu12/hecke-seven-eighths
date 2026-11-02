import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedDualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminalMass

set_option linter.unusedSectionVars false

/-!
# Sharp original coefficients in the same one-pool terminal sum

The individual main and valuation-one, -six and -seven calibrations
already use the exact original numerator and its divisor count.
Their central degree is combined with the first allowance before the
single original pool density is estimated. Empty actual fibres cost
zero and need no post-pool divisibility assertion.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory
open UniqueFactorizationMonoid

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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}


variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

/-- Sum the normalized parts on the original four source sorts. The
normalizing allowance is the same on every tag, and the pool density
is used exactly once. -/
theorem original_pool_terminal_normalized_sum
    {ι : Type*} (d : FirstGaussPoolData C P ι) (f : PoolSourceTag P → ℝ)
    (coefficient budget allowance Mmax : ℝ) (hcoefficient : 0 ≤ coefficient)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hterm : ∀ b, f b / Z ^ allowance ≤
      coefficient * poolTagNormCharge P b * Z ^ budget) :
    ((4 / d.density) * ∑ b, d.tagWeight b * f b) / Z ^ allowance ≤
      poolTerminalConstant K ell Mmax * coefficient * Z ^ (budget + eps) := by
  sorry

namespace ActualPoolStages.DualTerminalCalibration

variable {ι : Type*} {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)

/-- The sharp zero amplitude is required only for a nonempty original
row fibre. Its first-divisor denominator survives the one-pool sum. -/
theorem zeroBudget_div_allowance_le_combined_profiles
    (ε Czero profile divisorNorm allowance loss shift Mmax : ℝ)
    (amplitudeExponent : PoolSourceTag P → ℝ) (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (htuples : ∀ b, (T.tag b).windows.multiplicity ≤ tupleCap)
    (hAmplitude : ∀ b, (s.tag b).fiber ≠ 0 →
      (T.tag b).zeroAmplitude ≤
        (profile * poolTagNormCharge P b / divisorNorm) * Z ^ amplitudeExponent b)
    (hbudget : ∀ b, (s.tag b).fiber ≠ 0 →
      amplitudeExponent b + (T.tag b).zeroProductExponent * ε ≤
        allowance + loss - shift - eps) :
    T.zeroBudget ε Czero / Z ^ allowance ≤
      (poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) * Czero * (tupleCap : ℝ) * profile) / divisorNorm) *
          Z ^ (loss - shift) := by
  sorry

/-- The same pool tags and density bound the full-Cartesian tail. The
cutoff saving pays its coarse numerator exponent before normalization. -/
theorem tailBudget_div_allowance_le_combined_profiles
    (Cerror profile divisorNorm allowance loss shift Mmax : ℝ)
    (amplitudeExponent : PoolSourceTag P → ℝ) (fiberCap tupleCap : ℕ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profile) (hdivisor : 0 ≤ divisorNorm)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (htuples : ∀ b, (T.tag b).windows.multiplicity ≤ tupleCap)
    (hAmplitude : ∀ b, (s.tag b).fiber ≠ 0 →
      (T.tag b).tailAmplitude ≤
        (profile * poolTagNormCharge P b / divisorNorm) * Z ^ amplitudeExponent b)
    (hbudget : ∀ b, (s.tag b).fiber ≠ 0 →
      amplitudeExponent b - Nsave ≤ allowance + loss - shift - eps) :
    T.tailBudget Cerror / Z ^ allowance ≤
      (poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) * Cerror * (tupleCap : ℝ) * profile) / divisorNorm) *
          Z ^ (loss - shift) := by
  sorry

end ActualPoolStages.DualTerminalCalibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_pool_terminal_normalized_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.zeroBudget_div_allowance_le_combined_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.tailBudget_div_allowance_le_combined_profiles
