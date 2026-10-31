import ActualRowBallResidualGoodPrimeBound
import ActualFixedBoxTotalNormDecay

/-!
UNCOMPILED / native 0. A scalar bound for the actual finite residual sum.
The fixed Schwartz test is absorbed into a constant selected before all
moving ideals, frequencies, Mellin parameters and radii. The radius loss
is proved by the original Schwartz all-radius estimate, not assumed as
a profile envelope. This file only supplies the good-prime branch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualScalarDraft

open NumberField IsDedekindDomain MeasureTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualProbeGaussFourierDraft ActualProbePairNormDraft ActualAdditiveGramDraft
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramMajorantDraft ActualRowBallDualChartDraft
open ActualDenominatorGramWeightDraft ActualRowBallResidualAnalyticDraft
open ActualRowBallResidualMaskedDraft ActualAllowedTotalNormProviderDraft
open ActualChoiceMaskedTotalNormDraft ActualGeneratorChoiceDraft
open ActualRowBallResidualGoodPrimeDraft ActualFixedBoxTotalNormSeminormDraft ActualFixedBoxTotalNormDecayDraft
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "gen" => probeGenerator K S w.D

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The original finite residual sum, with the original frequency j. -/
def rowBallResidualSum (P : ProbeData K S) (Y η : ℝ)
    (r : {r : ℝ // 0 < r}) (C D : E) (j : NZ) : ℂ :=
  let rows := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
  let I : E → E := fun M => exteriorMul K S C (exteriorMul K S D M)
  ∑ mn ∈ mobiusResidualPairs K S C D rows rows,
    rowBallDualSpectralCoefficient K w.S μv P P.denominator.toSmoothAnnularTest
      Y η r (Quotient.mk _ j) (I mn.1) (I mn.2) *
    thetaChartCorrelationExtension K S P.arithmetic C
      (exteriorMul K S D mn.1, exteriorMul K S D mn.2) j

include μf in
/-- Every profile seminorm is eliminated from the actual good-prime bound.
The true frequency norm q_j is retained in both the radius and gain. -/
theorem exists_rowBallResidual_goodPrime_scalar_bound
    (P : ProbeData K S) (hP : P.arithmetic = w.D) (A : ℕ) (hA : 2 < A)
    (σ β : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσβ : σ ≤ β) :
    ∃ B : ℝ, ∃ J : ℕ, 0 ≤ B ∧ ∀ (C D : E) (j : NZ)
      (hj : w.D.generator C ∣ j.val),
      let k := thetaChartFrequencyQuotient K S w.D C j hj
      ∀ p : jointPlaces K (actualFrequencyIdeal K S (gen C)) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S (gen C)) (actualFrequencyIdeal_ne_zero K S k),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S (gen C)) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}),
      let q := Y / (exteriorNorm K S C * exteriorNorm K S D)
      let qj := (sIntegerElementNorm K S j).val
      ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
        B * (1 + |η|) ^ J *
          min ((qj / (r.val * Y ^ 2)) ^ (-σ)) ((qj / (r.val * Y ^ 2)) ^ (-β)) *
          exteriorNorm K S C * q ^ 2 * min 1 ((qj / q) ^ A) := by
  let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
  have hψ := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K w.S μf μv (rowBallFiniteFamily K w.S 1)
    (rowBallFiniteFamily_locallyConstant K w.S 1)
    (rowBallFiniteFamily_compactSupport K w.S 1)
  obtain ⟨t, B0, hB0, hb⟩ := exists_rowBallResidual_goodPrime_bound
    K w μf μv P hP A hA
  obtain ⟨s, C0, J, hC0, hs⟩ :=
    exists_fixedBoxTotalNormJointSeminormSum_min_decay_bound
      K w (denominatorGramWeight P.denominator) (contDiff_denominatorGramWeight P.denominator)
      P.denominator.lower P.denominator.upper P.denominator.lower_pos
      (tsupport_denominatorGramWeight P.denominator) ψ hψ.1.continuous hψ.2 σ β hσ hσ1 hσβ t
  let Φ := s.sup (schwartzSeminormFamily ℝ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (rowBallArchTest K w.S 1)
  have hΦ : 0 ≤ Φ := apply_nonneg _ _
  refine ⟨B0 * C0 * Φ, J, mul_nonneg (mul_nonneg hB0.le hC0) hΦ, ?_⟩
  intro C D j hj
  dsimp only
  intro p hpC hpJ Y η hY r
  have hqC : (Ideal.absNorm (actualFrequencyIdeal K S (gen C)) : ℝ) =
      exteriorNorm K S C := by
    have h := natCard_sIntegerPrincipalResidue_eq_productNorm K S
      (gen C).val (gen C).property
    simpa only [natCard_sIntegerPrincipalResidue K S (gen C).val (gen C).property, actualFrequencyIdeal,
      probeGenerator_norm_eq_exteriorNorm] using h
  have hbase := hb C D j hj p hpC hpJ Y η hY r
  dsimp only at hbase
  rw [residualFrequency_idealNorm_factor K w C j hj, hqC, div_div] at hbase
  let q := Y / (exteriorNorm K S C * exteriorNorm K S D)
  let qj := (sIntegerElementNorm K S j).val
  let R := residualJointRadius K w.S Y hY r j
  have hq : 0 < q := div_pos hY (mul_pos
    (exteriorNorm_pos_of_probeGenerator K S w.D C)
    (exteriorNorm_pos_of_probeGenerator K S w.D D))
  have hqj : 0 < qj := (sIntegerElementNorm K S j).property
  have hg : 0 ≤ min 1 ((qj / q) ^ A) :=
    le_min zero_le_one (pow_nonneg (div_pos hqj hq).le _)
  have hsemi := hs η (rowBallArchTest K w.S 1) R
  calc
    ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
        B0 * exteriorNorm K S C *
          fixedBoxTotalNormJointSeminormSum K w
            (denominatorGramWeight P.denominator) (contDiff_denominatorGramWeight P.denominator)
            P.denominator.lower P.denominator.upper P.denominator.lower_pos
            (tsupport_denominatorGramWeight P.denominator) ψ hψ.1.continuous hψ.2
            t η (rowBallArchTest K w.S 1) R * q ^ 2 * min 1 ((qj / q) ^ A) := by
      simpa only [rowBallResidualSum] using hbase
    _ ≤ B0 * exteriorNorm K S C *
        (C0 * Φ * (1 + |η|) ^ J * min (R.val ^ (-σ)) (R.val ^ (-β))) * q ^ 2 * min 1 ((qj / q) ^ A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsemi
            (mul_nonneg hB0.le (exteriorNorm_pos_of_probeGenerator K S w.D C).le))
          (sq_nonneg q)) hg
    _ = _ := by
      dsimp only [R, residualJointRadius, q, qj]
      ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualScalarDraft
