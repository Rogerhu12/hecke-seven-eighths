import ActualRowBallResidualScalarBound

/-!
UNCOMPILED / native 0. The actual finite residual sum has a no-cancellation
bound for every nonzero original frequency. Its exact finite-ideal identity
is used with the compensated whole-column trivial provider. The scalar
version then applies the proved original-Schwartz all-radius envelope.
The original frequency quotient, finite Fourier test and joint kernel are
retained. The external row-ball prefactor is not part of this residual sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualTrivialDraft

open NumberField IsDedekindDomain MeasureTheory
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
open ActualRowBallResidualScalarDraft ActualFixedBoxTotalNormSeminormDraft ActualFixedBoxTotalNormDecayDraft
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

/-- The exact actual finite sum is controlled at every frequency, without
any prime or multiplicity condition. The radius still uses the original j. -/
theorem exists_rowBallResidual_trivial_bound
    (P : ProbeData K S) (hP : P.arithmetic = w.D) :
    let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
    let hψ := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
      K w.S μf μv (rowBallFiniteFamily K w.S 1)
      (rowBallFiniteFamily_locallyConstant K w.S 1)
      (rowBallFiniteFamily_compactSupport K w.S 1)
    ∃ s : Finset (ℕ × ℕ), ∃ B : ℝ, 0 < B ∧ ∀ (C D : E) (j : NZ)
      (hj : w.D.generator C ∣ j.val),
      ∀ (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}),
      ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
      B * exteriorNorm K S C *
        fixedBoxTotalNormJointSeminormSum K w
          (denominatorGramWeight P.denominator) (contDiff_denominatorGramWeight P.denominator)
          P.denominator.lower P.denominator.upper P.denominator.lower_pos
          (tsupport_denominatorGramWeight P.denominator) ψ hψ.1.continuous hψ.2
          s η (rowBallArchTest K w.S 1) (residualJointRadius K w.S Y hY r j) *
        (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2 := by
  let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
  have hψ := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K w.S μf μv (rowBallFiniteFamily K w.S 1)
    (rowBallFiniteFamily_locallyConstant K w.S 1)
    (rowBallFiniteFamily_compactSupport K w.S 1)
  obtain ⟨s, B, hB, hb⟩ := exists_choiceMasked_totalNorm_originalDivisor_allScale_trivial_bound
    (K := K) (w := w) (ζ := w.D.root6) (hζ := w.D.primitive6) (σ := w.D.embedding)
    (hS6 := probeArithmetic_six_support K S w.D)
    (a := denominatorGramWeight P.denominator)
    (ha := contDiff_denominatorGramWeight P.denominator)
    (a0 := P.denominator.lower) (b0 := P.denominator.upper)
    (ha0 := P.denominator.lower_pos) (haSupport := tsupport_denominatorGramWeight P.denominator)
    (ψ := ψ) (hψ := hψ.1.continuous) (hψsupport := hψ.2)
  refine ⟨s, B, hB, ?_⟩
  intro C D j hj Y η hY r
  have hN : 0 < Y / exteriorNorm K S C :=
    div_pos hY (exteriorNorm_pos_of_probeGenerator K S w.D C)
  have hqC : (Ideal.absNorm (actualFrequencyIdeal K S (gen C)) : ℝ) =
      exteriorNorm K S C := by
    have h := natCard_sIntegerPrincipalResidue_eq_productNorm K S
      (gen C).val (gen C).property
    simpa only [natCard_sIntegerPrincipalResidue K S (gen C).val (gen C).property, actualFrequencyIdeal,
      probeGenerator_norm_eq_exteriorNorm] using h
  have h := hb (gen D) (gen C) (thetaChartFrequencyQuotient K S w.D C j hj)
    η (rowBallArchTest K w.S 1) (residualJointRadius K w.S Y hY r j)
    (Y / exteriorNorm K S C) hN
  unfold rowBallResidualSum
  rw [rowBallResidual_sum_eq_masked_columns K w μv P hP Y η hY r C D j hj]
  simpa only [choiceMaskedTotalNormAnnularJointSummand_allowedGenerator,
    probeGenerator_norm_eq_exteriorNorm, hqC, div_div] using h

include μf in
/-- A scalar bound for the actual exceptional-frequency consumer. The
fixed test is absorbed before C,D,j,Y,eta,r move; no frequency gain occurs. -/
theorem exists_rowBallResidual_trivial_scalar_bound
    (P : ProbeData K S) (hP : P.arithmetic = w.D)
    (σ β : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσβ : σ ≤ β) :
    ∃ B : ℝ, ∃ J : ℕ, 0 ≤ B ∧ ∀ (C D : E) (j : NZ)
      (hj : w.D.generator C ∣ j.val),
      ∀ (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}),
      let q := Y / (exteriorNorm K S C * exteriorNorm K S D)
      let qj := (sIntegerElementNorm K S j).val
      ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
        B * (1 + |η|) ^ J *
          min ((qj / (r.val * Y ^ 2)) ^ (-σ)) ((qj / (r.val * Y ^ 2)) ^ (-β)) *
          exteriorNorm K S C * q ^ 2 := by
  let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
  have hψ := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K w.S μf μv (rowBallFiniteFamily K w.S 1)
    (rowBallFiniteFamily_locallyConstant K w.S 1)
    (rowBallFiniteFamily_compactSupport K w.S 1)
  obtain ⟨t, B0, hB0, hb⟩ := exists_rowBallResidual_trivial_bound K w μf μv P hP
  obtain ⟨s, C0, J, hC0, hs⟩ :=
    exists_fixedBoxTotalNormJointSeminormSum_min_decay_bound
      K w (denominatorGramWeight P.denominator) (contDiff_denominatorGramWeight P.denominator)
      P.denominator.lower P.denominator.upper P.denominator.lower_pos
      (tsupport_denominatorGramWeight P.denominator) ψ hψ.1.continuous hψ.2 σ β hσ hσ1 hσβ t
  let Φ := s.sup (schwartzSeminormFamily ℝ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (rowBallArchTest K w.S 1)
  have hΦ : 0 ≤ Φ := apply_nonneg _ _
  refine ⟨B0 * C0 * Φ, J, mul_nonneg (mul_nonneg hB0.le hC0) hΦ, ?_⟩
  intro C D j hj Y η hY r
  dsimp only
  let q := Y / (exteriorNorm K S C * exteriorNorm K S D)
  let qj := (sIntegerElementNorm K S j).val
  let R := residualJointRadius K w.S Y hY r j
  have hbase := hb C D j hj Y η hY r
  have hsemi := hs η (rowBallArchTest K w.S 1) R
  calc
    ‖rowBallResidualSum K w μv P Y η r C D j‖ ≤
        B0 * exteriorNorm K S C *
          fixedBoxTotalNormJointSeminormSum K w
            (denominatorGramWeight P.denominator) (contDiff_denominatorGramWeight P.denominator)
            P.denominator.lower P.denominator.upper P.denominator.lower_pos
            (tsupport_denominatorGramWeight P.denominator) ψ hψ.1.continuous hψ.2
            t η (rowBallArchTest K w.S 1) R * q ^ 2 := hbase
    _ ≤ B0 * exteriorNorm K S C *
        (C0 * Φ * (1 + |η|) ^ J * min (R.val ^ (-σ)) (R.val ^ (-β))) * q ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsemi
          (mul_nonneg hB0.le (exteriorNorm_pos_of_probeGenerator K S w.D C).le))
        (sq_nonneg q)
    _ = _ := by
      dsimp only [R, residualJointRadius, q, qj]
      ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualTrivialDraft
