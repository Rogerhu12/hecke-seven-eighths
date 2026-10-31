import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualGaussHybridTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondTerminalAtoms

/-!
# Numerical terminal budgets for the signed source

The pure-dual zero and tail retain their original fibre, tuple count,
first-divisor denominator, and fixed profile amplitude. Their first
Fourier phase changes none of these quantities. Exponent allowances
are applied only after the original individual amplitude is proved.

The direct first-divisor estimates use exactly the same actual
coefficient atoms and no amplifier pool. Their retained support
multiplicity is the proved original divisor count, not an injection
assumption on residual columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory

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

theorem zeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) : 0 ≤ T.zeroBudget ε Czero := by
  unfold zeroBudget
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
      (mul_nonneg (Nat.cast_nonneg _) T.zeroAmplitude_nonneg))
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

theorem tailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) : 0 ≤ T.tailBudget Cerror := by
  unfold tailBudget
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
      (mul_nonneg (Nat.cast_nonneg _) T.windows.amplitude_nonneg))
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

/-- Exact decomposition on the original source.  The nonzero covered
cost keeps every original common-support, mask and occurrence label. -/
theorem coverHybridCost_eq_budgets (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC) (ε Cerror Czero : ℝ) :
    T.coverHybridCost LC RC exceptional ε Cerror Czero =
      T.zeroBudget ε Czero + (s.fiber : ℝ) * s.coverHybridNonzeroCost LC RC exceptional +
        T.tailBudget Cerror := by
  unfold coverHybridCost zeroBudget tailBudget
  ring

theorem zeroBudget_le_power (ε Czero profileConstant profileExponent budget : ℝ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hAmplitude : T.zeroAmplitude ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent + T.productExponent * ε ≤ budget) :
    T.zeroBudget ε Czero ≤
      ((s.fiber : ℝ) * Czero * T.windows.multiplicity * profileConstant) * Z ^ budget := by
  have h := terminal_atom_power_bound Z
    ((s.fiber : ℝ) * Czero * T.windows.multiplicity) profileConstant
    T.zeroAmplitude profileExponent (T.productExponent * ε) budget
    T.windows.base_ge_one (by positivity) hprofile hAmplitude hbudget
  convert h using 1 <;> unfold zeroBudget <;> ring

theorem tailBudget_le_power (Cerror profileConstant profileExponent budget : ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hAmplitude : T.tailAmplitude ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent - Nsave ≤ budget) :
    T.tailBudget Cerror ≤
      ((s.fiber : ℝ) * Cerror * T.windows.multiplicity * profileConstant) * Z ^ budget := by
  have h := terminal_atom_power_bound Z
    ((s.fiber : ℝ) * Cerror * T.windows.multiplicity) profileConstant
    T.tailAmplitude profileExponent (-Nsave) budget
    T.windows.base_ge_one (by positivity) hprofile hAmplitude (by linarith)
  convert h using 1 <;> unfold tailBudget <;> ring

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem fourierPhase_zeroBudget (x : ι → W) (ξ : W) (ε Czero : ℝ) :
    (T.fourierPhase x ξ).zeroBudget ε Czero = T.zeroBudget ε Czero := rfl

theorem fourierPhase_tailBudget (x : ι → W) (ξ : W) (Cerror : ℝ) :
    (T.fourierPhase x ξ).tailBudget Cerror = T.tailBudget Cerror := rfl

variable [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

theorem integral_fourierPhase_zeroBudget (F : 𝓢(W, ℂ)) (x : ι → W) (ε Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).zeroBudget ε Czero ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * T.zeroBudget ε Czero := by
  simp only [fourierPhase_zeroBudget, integral_const, smul_eq_mul]

theorem integral_fourierPhase_tailBudget (F : 𝓢(W, ℂ)) (x : ι → W) (Cerror : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).tailBudget Cerror ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * T.tailBudget Cerror := by
  simp only [fourierPhase_tailBudget, integral_const, smul_eq_mul]

end ActualGaussStage.DualTerminalCalibration

private theorem dual_terminal_allowance_power_cancel
    (Z allowance loss coefficient : ℝ) (hZ : 0 < Z) :
    (coefficient * Z ^ (allowance + loss)) / Z ^ allowance =
      coefficient * Z ^ loss := by
  rw [mul_div_assoc, ← Real.rpow_sub hZ]
  congr 2
  ring

namespace ActualGaussStage.DualResidualTerminalWindows

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {S : Ideal (𝓞 K)} {slots k : ℕ} {B Z Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}
variable {atoms : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
  G.columns G.coefficient S slots B}
variable (T : s.DualResidualTerminalWindows atoms sTail sZero k Z Lmax Nsave decay)

def zeroExponent : ℝ :=
  T.zeroProfileExponent + T.zeroColumnExponent +
    T.inverseRadiusExponent + T.productExponent / 2

/-- The direct zero budget is calibrated from individual original
residual profiles and exact support-tuple metadata. -/
theorem direct_zeroBudget_div_allowance_le
    (D : Ideal (𝓞 K))
    (hmult : T.windows.multiplicity = idealDivisorCount (D ^ 2) ^ k)
    (ε Czero profileConstant allowance loss : ℝ) (fiberCap maskCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hfiber : s.fiber ≤ fiberCap) (hmask : s.mask.card ≤ maskCap)
    (hraw : T.zeroProfileConstant ≤ profileConstant)
    (hbudget : T.zeroExponent + T.productExponent * ε ≤ allowance + loss) :
    T.calibration.zeroBudget ε Czero / Z ^ allowance ≤
      (directFirstDivisorZeroCoefficient B Czero profileConstant slots k fiberCap maskCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hB : 0 ≤ B ^ slots := pow_nonneg (zero_le_one.trans atoms.bound_ge_one) _
  have hcost : 0 ≤ B ^ slots * profileConstant * (2 : ℝ) ^ maskCap /
      (Ideal.absNorm S : ℝ) := by positivity
  have hAmplitude : T.calibration.zeroAmplitude ≤
      (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ)) *
        Z ^ T.zeroExponent := by
    rw [T.calibration_zeroAmplitude_power]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hraw hB)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmask)
      (pow_nonneg (by norm_num) _) (mul_nonneg hB hprofile)
  have hpart := T.calibration.zeroBudget_le_power ε Czero
    (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ))
    T.zeroExponent (allowance + loss) hC hcost hAmplitude hbudget
  have hcounts : (s.fiber : ℝ) * T.calibration.windows.multiplicity ≤
      (fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k : ℕ) := by
    change (s.fiber : ℝ) * (T.windows.multiplicity : ℝ) ≤ _
    rw [hmult]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber) (Nat.cast_nonneg _)
  have htotal : T.calibration.zeroBudget ε Czero ≤
      (directFirstDivisorZeroCoefficient B Czero profileConstant slots k fiberCap maskCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ (allowance + loss) := by
    apply hpart.trans
    convert mul_le_mul_of_nonneg_right hcounts
      (mul_nonneg (mul_nonneg hC hcost) (Real.rpow_nonneg hz.le (allowance + loss)))
      using 1 <;> simp only [directFirstDivisorZeroCoefficient] <;> ring
  exact (div_le_div_of_nonneg_right htotal (Real.rpow_nonneg hz.le _)).trans_eq
    (dual_terminal_allowance_power_cancel Z allowance loss _ hz)

/-- The direct tail uses the same original coefficient atoms and
support fibres; only its primitive residual-profile decay ledger differs. -/
theorem direct_tailBudget_div_allowance_le
    (D : Ideal (𝓞 K))
    (hmult : T.windows.multiplicity = idealDivisorCount (D ^ 2) ^ k)
    (Cerror profileConstant profileExponent allowance loss : ℝ) (fiberCap : ℕ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hfiber : s.fiber ≤ fiberCap)
    (hraw : T.tailProfileConstant ≤ profileConstant * Z ^ profileExponent)
    (hbudget : profileExponent - Nsave ≤ allowance + loss) :
    T.calibration.tailBudget Cerror / Z ^ allowance ≤
      (directFirstDivisorTailCoefficient B Cerror profileConstant slots k fiberCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hB : 0 ≤ B ^ slots := pow_nonneg (zero_le_one.trans atoms.bound_ge_one) _
  have hcost : 0 ≤ B ^ slots * profileConstant / (Ideal.absNorm S : ℝ) := by positivity
  have hAmplitude : T.calibration.tailAmplitude ≤
      (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ)) * Z ^ profileExponent := by
    rw [T.calibration_tailAmplitude]
    convert mul_le_mul_of_nonneg_left hraw atoms.scalarCost_nonneg using 1 <;>
      dsimp only [FirstDivisorCoefficientAtoms.scalarCost] <;> ring
  have hpart := T.calibration.tailBudget_le_power Cerror
    (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ))
    profileExponent (allowance + loss) hC hcost hAmplitude hbudget
  have hcounts : (s.fiber : ℝ) * T.calibration.windows.multiplicity ≤
      (fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k : ℕ) := by
    change (s.fiber : ℝ) * (T.windows.multiplicity : ℝ) ≤ _
    rw [hmult]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber) (Nat.cast_nonneg _)
  have htotal : T.calibration.tailBudget Cerror ≤
      (directFirstDivisorTailCoefficient B Cerror profileConstant slots k fiberCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ (allowance + loss) := by
    apply hpart.trans
    convert mul_le_mul_of_nonneg_right hcounts
      (mul_nonneg (mul_nonneg hC hcost) (Real.rpow_nonneg hz.le (allowance + loss)))
      using 1 <;> simp only [directFirstDivisorTailCoefficient] <;> ring
  exact (div_le_div_of_nonneg_right htotal (Real.rpow_nonneg hz.le _)).trans_eq
    (dual_terminal_allowance_power_cancel Z allowance loss _ hz)

end ActualGaussStage.DualResidualTerminalWindows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.zeroBudget_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.integral_fourierPhase_zeroBudget
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.direct_zeroBudget_div_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.direct_tailBudget_div_allowance_le
