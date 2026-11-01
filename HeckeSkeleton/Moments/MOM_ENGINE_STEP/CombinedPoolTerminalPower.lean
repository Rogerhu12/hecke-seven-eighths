import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedDualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminalMass

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
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  calc
    _ = (4 / d.density) * ∑ b, d.tagWeight b * (f b / Z ^ allowance) := by
      rw [mul_div_assoc, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ (4 / d.density) * ∑ b, d.tagWeight b *
        (coefficient * poolTagNormCharge P b * Z ^ budget) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hterm b) (d.tagWeight_nonneg b))
        (div_nonneg (by norm_num) d.density_pos.le)
    _ = (4 / d.density) * ∑ b,
        (d.tagWeight b * poolTagNormCharge P b) * (coefficient * Z ^ budget) := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ((4 / d.density) * ∑ b,
        d.tagWeight b * poolTagNormCharge P b) * (coefficient * Z ^ budget) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (poolTerminalConstant K ell Mmax * Z ^ eps) *
        (coefficient * Z ^ budget) :=
      mul_le_mul_of_nonneg_right (d.tag_norm_charge_mass_le Mmax hrow hlarge)
        (mul_nonneg hcoefficient (Real.rpow_nonneg hz.le _))
    _ = _ := by rw [Real.rpow_add hz]; ring

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
  have hparts (b : PoolSourceTag P) :
      (T.tag b).zeroBudget ε Czero / Z ^ allowance ≤
        (((fiberCap : ℝ) * Czero * (tupleCap : ℝ) * profile) / divisorNorm) *
          poolTagNormCharge P b * Z ^ (loss - shift - eps) := by
    have h := (T.tag b).zeroBudget_div_allowance_le_of_nonzero_fiber
      ε Czero (profile * poolTagNormCharge P b) divisorNorm
      (amplitudeExponent b) allowance (loss - eps) shift fiberCap tupleCap
      hC (mul_nonneg hprofile (poolTagNormCharge_nonneg b)) hdivisor
      (hfiber b) (htuples b) (hAmplitude b) (by intro hf; linarith [hbudget b hf])
    rw [show loss - eps - shift = loss - shift - eps by ring] at h
    convert h using 1 <;> ring
  have h := original_pool_terminal_normalized_sum d
    (fun b => (T.tag b).zeroBudget ε Czero)
    (((fiberCap : ℝ) * Czero * (tupleCap : ℝ) * profile) / divisorNorm)
    (loss - shift - eps) allowance Mmax (by positivity) hrow hlarge hparts
  rw [show loss - shift - eps + eps = loss - shift by ring] at h
  unfold zeroBudget
  convert h using 1 <;> ring

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
  have hparts (b : PoolSourceTag P) :
      (T.tag b).tailBudget Cerror / Z ^ allowance ≤
        (((fiberCap : ℝ) * Cerror * (tupleCap : ℝ) * profile) / divisorNorm) *
          poolTagNormCharge P b * Z ^ (loss - shift - eps) := by
    have h := (T.tag b).tailBudget_div_allowance_le_of_nonzero_fiber
      Cerror (profile * poolTagNormCharge P b) divisorNorm
      (amplitudeExponent b) allowance (loss - eps) shift fiberCap tupleCap
      hC (mul_nonneg hprofile (poolTagNormCharge_nonneg b)) hdivisor
      (hfiber b) (htuples b) (hAmplitude b) (by intro hf; linarith [hbudget b hf])
    rw [show loss - eps - shift = loss - shift - eps by ring] at h
    convert h using 1 <;> ring
  have h := original_pool_terminal_normalized_sum d
    (fun b => (T.tag b).tailBudget Cerror)
    (((fiberCap : ℝ) * Cerror * (tupleCap : ℝ) * profile) / divisorNorm)
    (loss - shift - eps) allowance Mmax (by positivity) hrow hlarge hparts
  rw [show loss - shift - eps + eps = loss - shift by ring] at h
  unfold tailBudget
  convert h using 1 <;> ring

end ActualPoolStages.DualTerminalCalibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_pool_terminal_normalized_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.zeroBudget_div_allowance_le_combined_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.tailBudget_div_allowance_le_combined_profiles
