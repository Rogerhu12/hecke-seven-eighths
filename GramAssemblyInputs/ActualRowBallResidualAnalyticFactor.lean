import ActualScaledColumnUnitReconstruction
import ActualRowBallDualChartIntegrand
import ActualDenominatorGramWeight

/-!
UNCOMPILED / native 0. Exact fixed-frequency analytic factor at the original
residual ideals C*(D*M_i). The scaled actual columns use gen(D)*gen(M_i),
not a multiplicativity assertion for the chosen generator function.
The orbital profile depends only on their proved total norms q_I/Y.
The original nonzero frequency j, both finite fibres and Haar measures
remain unchanged. No field/Jacobian factor or outer Y^(-3) is absorbed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualAnalyticDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualProbePairNormDraft ActualProbeGaussFourierDraft
open ActualGramMajorantDraft ActualRowBallDualChartDraft
open ActualDenominatorGramWeightDraft
open HeckeGeneral.Characters.ActualGramJointChartDraft
open HeckeGeneral.Analysis.ActualScaledColumnUnitDraft
open HeckeGeneral.Analysis.ActualClearedJointPeriodicDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K SF
local notation "NZ" => NonzeroRingElements (Set.integer SF K)

private theorem exteriorNorm_mul (I J : E) :
    exteriorNorm K SF (exteriorMul K SF I J) =
      exteriorNorm K SF I * exteriorNorm K SF J := by
  change ((Ideal.absNorm (I.val.val * J.val.val) : ℕ) : ℝ) = _
  simp only [map_mul, Nat.cast_mul, exteriorNorm]

/-- Each actual product column has the exact original denominator norm,
including the finite-S contribution. No chosen-generator equality is used. -/
theorem scaledGeneratorProduct_totalNorm (Θ : ThetaArithmeticData K SF)
    (C D M : E) (Y : ℝ) (hY : 0 < Y) :
    traceArchProductNorm K
        (scaledColumnArch K SF
          (divisorColumn K SF (probeGenerator K SF Θ D) (probeGenerator K SF Θ M))
          (Y / exteriorNorm K SF C)
          (div_pos hY (exteriorNorm_pos_of_probeGenerator K SF Θ C))).val *
      sFiniteProductNorm K SF
        (sLocalNonzeroIntegerDiagonal K SF
          (divisorColumn K SF (probeGenerator K SF Θ D) (probeGenerator K SF Θ M))).2 =
      exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M)) / Y := by
  rw [scaledColumn_totalNorm]
  have hprod : (sIntegerElementNorm K SF
      (divisorColumn K SF (probeGenerator K SF Θ D) (probeGenerator K SF Θ M))).val =
      exteriorNorm K SF D * exteriorNorm K SF M :=
    probePairGenerator_norm_eq K SF Θ D M
  rw [hprod, exteriorNorm_mul K S C (exteriorMul K SF D M), exteriorNorm_mul K S D M]
  field_simp [(exteriorNorm_pos_of_probeGenerator K SF Θ C).ne', hY.ne'] <;> ring

/-- True undilated nonzero dual radius, before removal of a common row
factor. In particular no extra q_C occurs at the supplied frequency j. -/
def residualJointRadius (Y : ℝ) (hY : 0 < Y)
    (r : {r : ℝ // 0 < r}) (j : NZ) : {r : ℝ // 0 < r} :=
  ⟨(sIntegerElementNorm K SF j).val / (r.val * Y ^ 2),
    div_pos (sIntegerElementNorm K SF j).property (mul_pos r.property (pow_pos hY 2))⟩

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The unsplit compensated joint factor is exactly the same total Mellin
phase times the original row-ball dual orbital profile. -/
theorem scaledColumnFactor_eq_rowBallProfile (P : ProbeData K SF)
    (C D M₁ M₂ : E) (Y η : ℝ) (hY : 0 < Y)
    (r : {r : ℝ // 0 < r}) (j : NZ) :
    scaledColumnCompensatedJointFactor K SF
        (sIntegerFiniteFourierTestFunction K S μv (rowBallFiniteFamily K S 1))
        (probeGenerator K SF P.arithmetic D) η (rowBallArchTest K S 1)
        (residualJointRadius K S Y hY r j) (Y / exteriorNorm K SF C)
        (probeGenerator K SF P.arithmetic M₁, probeGenerator K SF P.arithmetic M₂) =
      traceRealMovingPhase η
        (Real.log (exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₁)) / Y) -
          Real.log (exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₂)) / Y)) *
        rowBallDualPairProfile K S μv P
          (exteriorMul K SF C (exteriorMul K SF D M₁))
          (exteriorMul K SF C (exteriorMul K SF D M₂)) r (Quotient.mk _ j) := by
  let n₁ := divisorColumn K SF (probeGenerator K SF P.arithmetic D)
    (probeGenerator K SF P.arithmetic M₁)
  let n₂ := divisorColumn K SF (probeGenerator K SF P.arithmetic D)
    (probeGenerator K SF P.arithmetic M₂)
  have hN : 0 < Y / exteriorNorm K SF C :=
    div_pos hY (exteriorNorm_pos_of_probeGenerator K SF P.arithmetic C)
  dsimp only [scaledColumnCompensatedJointFactor, originalJointFactor]
  rw [← scaledColumnArch_val K SF (divisorColumn K SF (probeGenerator K SF P.arithmetic D)
      (probeGenerator K SF P.arithmetic M₁)) (Y / exteriorNorm K SF C) hN,
    ← scaledColumnArch_val K SF (divisorColumn K SF (probeGenerator K SF P.arithmetic D)
      (probeGenerator K SF P.arithmetic M₂)) (Y / exteriorNorm K SF C) hN]
  rw [traceJointOrbitalKernel_totalNormRadius]
  unfold sUnitMellinPhase
  simp only [scaledGeneratorProduct_totalNorm K S P.arithmetic C D M₁ Y hY,
    scaledGeneratorProduct_totalNorm K S P.arithmetic C D M₂ Y hY]
  congr 1
  unfold rowBallDualPairProfile
  congr 1
  apply Subtype.ext
  dsimp only
  rw [sIntegerOrbitNorm_mk]
  change ((sIntegerElementNorm K SF j).val / (r.val * Y ^ 2)) /
      ((exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₁)) / Y) *
        (exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₂)) / Y)) =
    (r.val * (sIntegerElementNorm K SF
      (additiveGramPairModulus K S P
        (exteriorMul K SF C (exteriorMul K SF D M₁))
        (exteriorMul K SF C (exteriorMul K SF D M₂)))).val)⁻¹ *
      (sIntegerElementNorm K SF j).val
  have hmod : (sIntegerElementNorm K SF
      (additiveGramPairModulus K S P
        (exteriorMul K SF C (exteriorMul K SF D M₁))
        (exteriorMul K SF C (exteriorMul K SF D M₂)))).val =
      exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₁)) *
        exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₂)) :=
    probePairGenerator_norm_eq K SF P.arithmetic _ _
  rw [hmod]
  field_simp [hY.ne', r.property.ne',
    (exteriorNorm_pos_of_probeGenerator K SF P.arithmetic
      (exteriorMul K SF C (exteriorMul K SF D M₁))).ne',
    (exteriorNorm_pos_of_probeGenerator K SF P.arithmetic
      (exteriorMul K SF C (exteriorMul K SF D M₂))).ne'] <;> ring

/-- Actual c=1 spectral coefficient at I_i=C*(D*M_i), with the real
smooth denominator weight and the original frequency/measure conventions.
The separate outer r^(-1)*Y^(-3)*fieldFactor is unchanged. -/
theorem rowBallDualSpectralCoefficient_eq_scaledJointFactor
    (P : ProbeData K SF) (C D M₁ M₂ : E) (Y η : ℝ) (hY : 0 < Y)
    (r : {r : ℝ // 0 < r}) (j : NZ) :
    rowBallDualSpectralCoefficient K S μv P P.denominator.toSmoothAnnularTest
        Y η r (Quotient.mk _ j)
        (exteriorMul K SF C (exteriorMul K SF D M₁))
        (exteriorMul K SF C (exteriorMul K SF D M₂)) =
      scaledColumnCompensatedJointFactor K SF
        (sIntegerFiniteFourierTestFunction K S μv (rowBallFiniteFamily K S 1))
        (probeGenerator K SF P.arithmetic D) η (rowBallArchTest K S 1)
        (residualJointRadius K S Y hY r j) (Y / exteriorNorm K SF C)
        (probeGenerator K SF P.arithmetic M₁, probeGenerator K SF P.arithmetic M₂) *
      (denominatorGramWeight P.denominator
        (exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₁)) / Y) : ℂ) *
      (denominatorGramWeight P.denominator
        (exteriorNorm K SF (exteriorMul K SF C (exteriorMul K SF D M₂)) / Y) : ℂ) := by
  unfold rowBallDualSpectralCoefficient
  rw [actualDenominator_pairCoefficient_eq_realWeight_phase K SF P Y η hY,
    scaledColumnFactor_eq_rowBallProfile K S μv P C D M₁ M₂ Y η hY r j]
  ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualAnalyticDraft
