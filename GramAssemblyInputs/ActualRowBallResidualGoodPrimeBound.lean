import ActualRowBallResidualMaskedIdentity
import ActualAllowedTotalNormProviderIdentity
import HeckeGeneral.Bridge.SLocalFiniteFourier
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-!
UNCOMPILED / native 0. The actual finite residual-ideal sum consumes the
proved whole-column provider through its exact ideal/unit identity.
The finite Fourier test and its regularity are constructed from the
fixed row-ball majorant. The constant and seminorm set precede all moving
ideals, frequencies, radii and Mellin parameters. This is the good-prime
part only; no estimate for the exceptional frequencies is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualGoodPrimeDraft

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
open ActualChoiceMaskedTotalNormDraft ActualGeneratorChoiceDraft ActualGramJointMeanDraft
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

/-- Division of the actual frequency gives q_j=q_C q_k, including all
finite-place factors. No multiplicativity of the generator choice is used. -/
theorem residualFrequency_elementNorm_factor (C : E) (j : NZ)
    (hj : w.D.generator C ∣ j.val) :
    exteriorNorm K S C *
      (sIntegerElementNorm K S (thetaChartFrequencyQuotient K S w.D C j hj)).val =
        (sIntegerElementNorm K S j).val := by
  have hprod : sIntegerNonzeroMul K S (gen C)
      (thetaChartFrequencyQuotient K S w.D C j hj) = j := by
    apply Subtype.ext
    exact thetaChartFrequencyQuotient_factor K S w.D C j hj
  have h := sIntegerElementNorm_nonzeroMul K S (gen C)
    (thetaChartFrequencyQuotient K S w.D C j hj)
  rw [hprod, probeGenerator_norm_eq_exteriorNorm] at h
  exact h.symm

/-- The product q_c q_k in the whole-column bound is the norm of the
original frequency j. This is the same shell parameter used for counting. -/
theorem residualFrequency_idealNorm_factor (C : E) (j : NZ)
    (hj : w.D.generator C ∣ j.val) :
    (Ideal.absNorm (actualFrequencyIdeal K S (gen C)) : ℝ) *
      (Ideal.absNorm (actualFrequencyIdeal K S
        (thetaChartFrequencyQuotient K S w.D C j hj)) : ℝ) =
        (sIntegerElementNorm K S j).val := by
  have hn (n : NZ) : (Ideal.absNorm (actualFrequencyIdeal K S n) : ℝ) =
      (sIntegerElementNorm K S n).val := by
    simpa only [natCard_sIntegerPrincipalResidue K S n.val n.property, actualFrequencyIdeal] using
      natCard_sIntegerPrincipalResidue_eq_productNorm K S n.val n.property
  rw [hn, hn, probeGenerator_norm_eq_exteriorNorm]
  exact residualFrequency_elementNorm_factor K w C j hj

/-- The actual residual sum has the all-scale mean-zero gain at every
prime outside c whose frequency multiplicity is not divisible by six.
The radius is q_j/(rY²), and the remaining column scale is Y/(q_C q_D).
No pointwise identification, convergence, smoothness or Fourier-closure
claim is an additional hypothesis. -/
theorem exists_rowBallResidual_goodPrime_bound
    (P : ProbeData K S) (hP : P.arithmetic = w.D) (A : ℕ) (hA : 2 < A) :
    let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
    let hψ := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
      K w.S μf μv (rowBallFiniteFamily K w.S 1)
      (rowBallFiniteFamily_locallyConstant K w.S 1)
      (rowBallFiniteFamily_compactSupport K w.S 1)
    ∃ s : Finset (ℕ × ℕ), ∃ B : ℝ, 0 < B ∧ ∀ (C D : E) (j : NZ)
      (hj : w.D.generator C ∣ j.val),
      let k := thetaChartFrequencyQuotient K S w.D C j hj
      ∀ p : jointPlaces K (actualFrequencyIdeal K S (gen C)) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S (gen C)) (actualFrequencyIdeal_ne_zero K S k),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S (gen C)) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}),
      let rows := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
      let I : E → E := fun M => exteriorMul K S C (exteriorMul K S D M)
      ‖∑ mn ∈ mobiusResidualPairs K S C D rows rows,
        rowBallDualSpectralCoefficient K w.S μv P P.denominator.toSmoothAnnularTest
          Y η r (Quotient.mk _ j) (I mn.1) (I mn.2) *
        thetaChartCorrelationExtension K S P.arithmetic C
          (exteriorMul K S D mn.1, exteriorMul K S D mn.2) j‖ ≤
      B * (Ideal.absNorm (actualFrequencyIdeal K S (gen C)) : ℝ) *
        fixedBoxTotalNormJointSeminormSum K w
          (denominatorGramWeight P.denominator) (contDiff_denominatorGramWeight P.denominator)
          P.denominator.lower P.denominator.upper P.denominator.lower_pos
          (tsupport_denominatorGramWeight P.denominator) ψ hψ.1.continuous hψ.2
          s η (rowBallArchTest K w.S 1) (residualJointRadius K w.S Y hY r j) *
        ((Y / exteriorNorm K S C) / exteriorNorm K S D) ^ 2 *
        min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S (gen C)) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
          ((Y / exteriorNorm K S C) / exteriorNorm K S D)) ^ A) := by
  let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
  have hψ := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K w.S μf μv (rowBallFiniteFamily K w.S 1)
    (rowBallFiniteFamily_locallyConstant K w.S 1)
    (rowBallFiniteFamily_compactSupport K w.S 1)
  obtain ⟨s, B, hB, hb⟩ := exists_choiceMasked_totalNorm_originalDivisor_allScale_min_bound
    (K := K) (w := w) (ζ := w.D.root6) (hζ := w.D.primitive6) (σ := w.D.embedding)
    (hS6 := probeArithmetic_six_support K S w.D)
    (a := denominatorGramWeight P.denominator)
    (ha := contDiff_denominatorGramWeight P.denominator)
    (a0 := P.denominator.lower) (b0 := P.denominator.upper)
    (ha0 := P.denominator.lower_pos) (haSupport := tsupport_denominatorGramWeight P.denominator)
    (ψ := ψ) (hψ := hψ.1.continuous) (hψsupport := hψ.2) A hA
  refine ⟨s, B, hB, ?_⟩
  intro C D j hj
  dsimp only
  intro p hpC hpJ Y η hY r
  have hN : 0 < Y / exteriorNorm K S C :=
    div_pos hY (exteriorNorm_pos_of_probeGenerator K S w.D C)
  have h := hb (gen D) (gen C) (thetaChartFrequencyQuotient K S w.D C j hj)
    p hpC hpJ η (rowBallArchTest K w.S 1) (residualJointRadius K w.S Y hY r j)
    (Y / exteriorNorm K S C) hN
  rw [rowBallResidual_sum_eq_masked_columns K w μv P hP Y η hY r C D j hj]
  simpa only [choiceMaskedTotalNormAnnularJointSummand_allowedGenerator,
    probeGenerator_norm_eq_exteriorNorm] using h

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualGoodPrimeDraft
