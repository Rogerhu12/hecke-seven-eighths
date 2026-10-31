import ActualAllowedChartCoefficient
import ActualGramResidualSupport
import ActualRowBallDualChartIntegrand

/-!
UNCOMPILED / native 0. The actual finite residual-ideal term in the
row-ball dual becomes a whole ideal-pair sum on the same allowed
generators. Its actual profile, Mellin coefficient and frequency quotient
are retained. This is an equality of sums, before any cancellation bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedResidualSumDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualProbeGaussFourierDraft ActualAdditiveGramDraft
open ActualGramJointChartCoverDraft ActualAllowedChartCoefficientDraft
open ActualGramResidualSupportDraft ActualRowBallDualChartDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "gen" => probeGenerator K S w.D

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Actual finite residual term equals the whole ideal-pair sum, with
the SAME P arithmetic identified with the supplied actual witness. -/
theorem rowBallResidual_sum_eq_allowed_tsum
    (P : ProbeData K S) (hP : P.arithmetic = w.D)
    (W : SmoothAnnularTest) (Y η : ℝ) (hY : 0 < Y)
    (r : {r : ℝ // 0 < r}) (C D : E) (j : NZ) (hj : w.D.generator C ∣ j.val) :
    let A := additiveGramIdealSupport K S W Y
    let I : E → E := fun M => exteriorMul K S C (exteriorMul K S D M)
    let corr : E × E → ℂ := fun mn =>
      originalChartCoefficient K S w.D.root6 w.D.primitive6 w.D.embedding
        (probeArithmetic_six_support K S w.D) (gen C)
        (thetaChartFrequencyQuotient K S w.D C j hj) (gen D) (gen mn.1) (gen mn.2)
    (∑ mn ∈ mobiusResidualPairs K S C D A A,
      rowBallDualSpectralCoefficient K w.S μv P W Y η r (Quotient.mk _ j)
        (I mn.1) (I mn.2) *
      thetaChartCorrelationExtension K S P.arithmetic C
        (exteriorMul K S D mn.1, exteriorMul K S D mn.2) j) =
    ∑' mn : E × E,
      rowBallDualSpectralCoefficient K w.S μv P W Y η r (Quotient.mk _ j)
        (I mn.1) (I mn.2) * corr mn := by
  dsimp only
  let corr : E × E → ℂ := fun mn =>
    originalChartCoefficient K S w.D.root6 w.D.primitive6 w.D.embedding
      (probeArithmetic_six_support K S w.D) (gen C)
      (thetaChartFrequencyQuotient K S w.D C j hj) (gen D) (gen mn.1) (gen mn.2)
  let B : E × E → ℂ := fun mn =>
    rowBallDualPairProfile K w.S μv P
      (exteriorMul K S C (exteriorMul K S D mn.1))
      (exteriorMul K S C (exteriorMul K S D mn.2)) r (Quotient.mk _ j) * corr mn
  have hterm (mn : E × E) :
      actualGramResidualWeight K S W Y η C D B mn =
        rowBallDualSpectralCoefficient K w.S μv P W Y η r (Quotient.mk _ j)
          (exteriorMul K S C (exteriorMul K S D mn.1))
          (exteriorMul K S C (exteriorMul K S D mn.2)) * corr mn := by
    dsimp only [actualGramResidualWeight, rowBallDualSpectralCoefficient, B]
    ring
  calc
    _ = ∑ mn ∈ mobiusResidualPairs K S C D
          (additiveGramIdealSupport K S W Y) (additiveGramIdealSupport K S W Y),
          actualGramResidualWeight K S W Y η C D B mn := by
      apply Finset.sum_congr rfl
      intro mn _hmn
      rw [hP, thetaChartCorrelationExtension_eq_allowedColumns K w C D mn.1 mn.2 j hj]
      exact (hterm mn).symm
    _ = ∑' mn : E × E, actualGramResidualWeight K S W Y η C D B mn :=
      actualGramResidualWeight_sum_eq_tsum K S W Y η hY C D B
    _ = _ := tsum_congr hterm

end HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedResidualSumDraft
