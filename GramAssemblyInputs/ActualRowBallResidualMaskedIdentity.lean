import ActualAllowedResidualSum
import ActualRowBallResidualAnalyticFactor
import ActualOriginalAnnularUnitReconstruction
import ActualAllowedPairEnumeration

/-!
UNCOMPILED / native 0. The original finite residual-ideal row-ball sum
equals the complete choice-masked S-integer column sum. Its actual
denominator, frequency quotient, two finite fibres and single compensated
joint kernel are retained. The actual denominator support supplies the
finite-support premise for the ideal/unit rearrangement. No Gram bound
is an input, and no exterior row-ball prefactor is absorbed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualMaskedDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualProbeGaussFourierDraft ActualAdditiveGramDraft
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramMajorantDraft ActualRowBallDualChartDraft ActualAllowedResidualSumDraft
open ActualDenominatorGramWeightDraft ActualRowBallResidualAnalyticDraft
open ActualOriginalAnnularUnitDraft ActualAllowedPairEnumerationDraft
open HeckeGeneral.Analysis.ActualScaledColumnUnitDraft
open ActualGeneratorChoiceDraft ActualProbePairNormDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "Γ" => sixthPowerUnits K S
local notation "gen" => probeGenerator K S w.D

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Exact actual finite-ideal to full masked-column identity. The frequency
is the quotient selected by the original hj, and the joint radius uses j
itself. The separate r⁻¹ Y⁻³ field factor remains outside this identity. -/
theorem rowBallResidual_sum_eq_masked_columns
    (P : ProbeData K S) (hP : P.arithmetic = w.D)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r})
    (C D : E) (j : NZ) (hj : w.D.generator C ∣ j.val) :
    let A := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
    let I : E → E := fun M => exteriorMul K S C (exteriorMul K S D M)
    let k := thetaChartFrequencyQuotient K S w.D C j hj
    let F := originalTotalNormAnnularSummand K S w.D.root6 w.D.primitive6
      w.D.embedding (probeArithmetic_six_support K S w.D)
      (denominatorGramWeight P.denominator)
      (sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1))
      (gen C) k (gen D) η (rowBallArchTest K w.S 1)
      (residualJointRadius K w.S Y hY r j) (Y / exteriorNorm K S C)
    (∑ mn ∈ mobiusResidualPairs K S C D A A,
      rowBallDualSpectralCoefficient K w.S μv P P.denominator.toSmoothAnnularTest
        Y η r (Quotient.mk _ j) (I mn.1) (I mn.2) *
      thetaChartCorrelationExtension K S P.arithmetic C
        (exteriorMul K S D mn.1, exteriorMul K S D mn.2) j) =
    ∑' m : NZ × NZ,
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.1).2 *
        choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.2).2 * F m := by
  dsimp only
  let I : E → E := fun M => exteriorMul K S C (exteriorMul K S D M)
  let a := denominatorGramWeight P.denominator
  let ψ := sIntegerFiniteFourierTestFunction K w.S μv (rowBallFiniteFamily K w.S 1)
  let φ := rowBallArchTest K w.S 1
  let R := residualJointRadius K w.S Y hY r j
  let N := Y / exteriorNorm K S C
  let k := thetaChartFrequencyQuotient K S w.D C j hj
  let corr : E × E → ℂ := fun mn =>
    originalChartCoefficient K S w.D.root6 w.D.primitive6 w.D.embedding
      (probeArithmetic_six_support K S w.D) (gen C) k (gen D) (gen mn.1) (gen mn.2)
  let F := originalTotalNormAnnularSummand K S w.D.root6 w.D.primitive6
    w.D.embedding (probeArithmetic_six_support K S w.D) a ψ
    (gen C) k (gen D) η φ R N
  have hN : 0 < N := div_pos hY (exteriorNorm_pos_of_probeGenerator K S w.D C)
  have hnorm (M : E) :
      (Ideal.absNorm (sIntegerModulusContraction K S
        (divisorColumn K S (gen D) (gen M)).val) : ℝ) / N =
        exteriorNorm K S (I M) / Y :=
    (scaledColumn_totalNorm_eq_idealNorm K S
      (divisorColumn K S (gen D) (gen M)) N hN).symm.trans
        (scaledGeneratorProduct_totalNorm K w.S w.D C D M Y hY)
  have hspec (mn : E × E) :
      rowBallDualSpectralCoefficient K w.S μv P P.denominator.toSmoothAnnularTest
        Y η r (Quotient.mk _ j) (I mn.1) (I mn.2) =
      scaledColumnCompensatedJointFactor K S ψ (gen D) η φ R N
        (gen mn.1, gen mn.2) *
        (a (exteriorNorm K S (I mn.1) / Y) : ℂ) *
        (a (exteriorNorm K S (I mn.2) / Y) : ℂ) := by
    simpa only [hP] using
      rowBallDualSpectralCoefficient_eq_scaledJointFactor K w.S μv P C D mn.1 mn.2
        Y η hY r j
  have hunit (mn : E × E) :
      (∑' uv : Γ × Γ, F
        (sIntegerOrbitTranslate K S Γ uv.1 (gen mn.1),
         sIntegerOrbitTranslate K S Γ uv.2 (gen mn.2))) =
      rowBallDualSpectralCoefficient K w.S μv P P.denominator.toSmoothAnnularTest
        Y η r (Quotient.mk _ j) (I mn.1) (I mn.2) * corr mn := by
    have h := originalTotalNormAnnularSummand_units_tsum K S
      w.D.root6 w.D.primitive6 w.D.embedding (probeArithmetic_six_support K S w.D)
      a ψ (gen C) k (gen D) (gen mn.1) (gen mn.2) η φ R N hN
    calc
      _ = corr mn *
          (scaledColumnCompensatedJointFactor K S ψ (gen D) η φ R N (gen mn.1, gen mn.2) *
            ((a (exteriorNorm K S (I mn.1) / Y) *
              a (exteriorNorm K S (I mn.2) / Y) : ℝ) : ℂ)) := by
        simpa only [hnorm mn.1, hnorm mn.2] using h
      _ = _ := by rw [hspec mn]; simp only [Complex.ofReal_mul]; ring
  have hfin : Function.HasFiniteSupport F :=
    originalTotalNormAnnularSummand_hasFiniteSupport K S
      w.D.root6 w.D.primitive6 w.D.embedding (probeArithmetic_six_support K S w.D)
      a P.denominator.lower P.denominator.upper P.denominator.lower_pos
      (tsupport_denominatorGramWeight P.denominator) ψ
      (gen C) k (gen D) η φ R N hN
  calc
    _ = ∑' mn : E × E,
        rowBallDualSpectralCoefficient K w.S μv P P.denominator.toSmoothAnnularTest
          Y η r (Quotient.mk _ j) (I mn.1) (I mn.2) * corr mn :=
      rowBallResidual_sum_eq_allowed_tsum K w μv P hP P.denominator.toSmoothAnnularTest
        Y η hY r C D j hj
    _ = ∑' mn : E × E, ∑' uv : Γ × Γ, F
        (sIntegerOrbitTranslate K S Γ uv.1 (gen mn.1),
         sIntegerOrbitTranslate K S Γ uv.2 (gen mn.2)) :=
      tsum_congr (fun mn => (hunit mn).symm)
    _ = _ := (tsum_choiceFiniteMask_pair_eq_idealPair_unitPair K w F hfin).symm

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualMaskedDraft
