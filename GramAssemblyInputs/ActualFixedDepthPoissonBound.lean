import ActualJointRadicalPeriodNorm
import ActualFixedSBoxDenominator

/-!
UNCOMPILED candidate. At the fixed depth 2H provided by the actual
S-valuation box, the arithmetic Poisson estimate has only Norm C * Norm J
in its moving norm ratio. The fixed S factor is absorbed in the constant.

The weight is the actual CRT/lattice weight, with proved magnitude and
mean zero. Identifying the entire original Gram sum after divisor-unit
transport and controlling its joint profile remain separate obligations.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualFixedDepthPoissonDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramPeriodNormDraft
open ActualMeanZeroProductPoissonDraft
open scoped Classical FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "N₀" => H + H

/-- Constant chosen before both moving ideals, the divisor, fibers,
centers, Schwartz input, scale and translation. The fixed depth is 2H. -/
theorem exists_uniform_fixedDepth_weight_poisson_bound (A : ℕ) (hA : 2 < A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ N₀) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (F : SchwartzMap (traceProductSpace K) ℂ) (X : ℝ), 0 < X →
      ∀ v : traceProductSpace K,
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N₀)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂) F X v‖ ≤
      C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F) * X ^ 2 *
        (((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / X) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_fixedChartLatticeWeight_bound K S ζ hζ σ hS6 Γ A hA
  obtain ⟨D, hD, hperiod⟩ := exists_fixedChartPeriodIdeal_norm_constant K S ζ hζ N₀
  refine ⟨C * D ^ A, mul_pos hC (pow_pos hD _), ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ F X hX v
  have hbase := hbound c k N₀ H a₁ a₂ d b₁ b₂ p hpC hpJ F X hX v
  let qC : ℝ := Ideal.absNorm (actualFrequencyIdeal K S c)
  let qJ : ℝ := Ideal.absNorm (actualFrequencyIdeal K S k)
  let qI : ℝ := Ideal.absNorm (fixedChartPeriodIdeal K S ζ hζ c k N₀).val
  let seminorm : ℝ := SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F)
  have hquot : qI / X ≤ D * (qC * qJ / X) := by
    calc
      _ ≤ (D * qC * qJ) / X := div_le_div_of_nonneg_right (hperiod c k) hX.le
      _ = _ := by ring
  have hqI : 0 ≤ qI / X := div_nonneg (Nat.cast_nonneg _) hX.le
  have hpow : (qI / X) ^ A ≤ D ^ A * (qC * qJ / X) ^ A := by
    simpa only [mul_pow] using pow_le_pow_left₀ hqI hquot A
  have hfac : 0 ≤ C * qC * seminorm * X ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _))
      (apply_nonneg _ _)) (sq_nonneg X)
  change ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N₀)
      (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂) F X v‖ ≤
    (C * D ^ A) * qC * seminorm * X ^ 2 * (qC * qJ / X) ^ A
  calc
    _ ≤ C * qC * seminorm * X ^ 2 * (qI / X) ^ A := hbase
    _ ≤ C * qC * seminorm * X ^ 2 * (D ^ A * (qC * qJ / X) ^ A) :=
      mul_le_mul_of_nonneg_left hpow hfac
    _ = _ := by ring

end HeckeGeneral.Analysis.ActualFixedDepthPoissonDraft
