import ActualGramRowBallPoissonReduction
import ActualThetaChartGcdMobius

/-!
UNCOMPILED / native 0. The actual row-ball nonzero dual, with c identically
one, is a genuinely summable original-sixth-unit orbit integrand. At each
nonzero representative its finite ideal-pair sum is exactly the B71
gcd/Mobius chart sum. Pair-dependent radii and the free row-ball Fourier
test remain unchanged. No cancellation or Gram bound is an input.

This does NOT identify the chosen-generator residual-ideal sum with the
whole S-integer annular column sum. That further identification requires
an actual Gamma partition and finite unit-sector/choice masks; a bound
for a whole complex sum cannot be applied to its chosen-generator subset.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualChartDraft

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualPairDivisorDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualAdditiveGramDraft ActualAdditiveGramFreeDraft
open ActualProbePairFourierDraft ActualProbePairOrbitalDraft
open ActualProbeGaussFourierDraft ActualGramMajorantDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K SF
local notation "E" => ExteriorIdeal K SF
local notation "NZ" => NonzeroRingElements (Set.integer SF K)
local notation "OQ" => SIntegerOrbits K SF Γ

local instance chart_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The unchanged free Fourier profile at the true pair radius. -/
def rowBallDualPairProfile (P : ProbeData K SF) (I J : E)
    (r : {r : ℝ // 0 < r}) (q : OQ) : ℂ :=
  sUnitOrbitalProfile K SF
    (sLocalTensorTestFunction K SF
      (traceSchwartzFourier K (rowBallArchTest K S 1))
      (sIntegerFiniteFourierTestFunction K S μv (rowBallFiniteFamily K S 1)))
    ⟨(additiveGramPairDualRadius K S P I J r).val *
        (sIntegerOrbitNorm K SF Γ q).val,
      mul_pos (additiveGramPairDualRadius K S P I J r).property
        (sIntegerOrbitNorm K SF Γ q).property⟩

/-- Actual c=1 coefficient times the pair-dependent profile. The profile
is part of the weight when applying the finite gcd/Mobius theorem. -/
def rowBallDualSpectralCoefficient (P : ProbeData K SF) (W : SmoothAnnularTest)
    (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : OQ) (I J : E) : ℂ :=
  actualAdditiveGramPairCoefficient K SF (fun _ => 1) W Y η I J *
    rowBallDualPairProfile K S μv P I J r q

/-- The genuine finite-IJ dual integrand, on the original Gamma quotient. -/
def rowBallDualIntegrand (P : ProbeData K SF) (W : SmoothAnnularTest)
    (Y η : ℝ) (r : {r : ℝ // 0 < r}) (q : OQ) : ℂ :=
  ∑ I ∈ additiveGramIdealSupport K SF W Y,
    ∑ J ∈ additiveGramIdealSupport K SF W Y,
      rowBallDualSpectralCoefficient K S μv P W Y η r q I J *
        probeOriginalCorrelationOrbitWeight K S P I J q

/-- Full residual families after gcd regrouping and Mobius insertion.
The artificial chart extension is used also on noncoprime residuals;
equality to the genuine correlation is needed only before insertion. -/
def rowBallDualChartIntegrand (P : ProbeData K SF) (W : SmoothAnnularTest)
    (Y η : ℝ) (r : {r : ℝ // 0 < r}) (j : NZ) : ℂ :=
  let A := additiveGramIdealSupport K SF W Y
  ∑ C ∈ finiteCommonParts K SF A A,
    ∑ T ∈ (residualPrimeEnvelope K SF C A A).powerset.attach,
      (moebius (primeProduct T.val) : ℂ) *
        ∑ mn ∈ mobiusResidualPairs K SF C (residualMobiusDivisor K SF C A A T) A A,
          rowBallDualSpectralCoefficient K S μv P W Y η r (Quotient.mk _ j)
            (exteriorMul K SF C
              (exteriorMul K SF (residualMobiusDivisor K SF C A A T) mn.1))
            (exteriorMul K SF C
              (exteriorMul K SF (residualMobiusDivisor K SF C A A T) mn.2)) *
          thetaChartCorrelationExtension K SF P.arithmetic C
            (exteriorPairDilation K SF (residualMobiusDivisor K SF C A A T) mn) j

/-- Exact fixed-frequency consumer, retaining all original pair weights,
conjugations and actual profile/radius data. No coprimality is assumed. -/
theorem rowBallDualIntegrand_mk_eq_chart (P : ProbeData K SF)
    (W : SmoothAnnularTest) (Y η : ℝ) (r : {r : ℝ // 0 < r}) (j : NZ) :
    rowBallDualIntegrand K S μv P W Y η r (Quotient.mk _ j) =
      rowBallDualChartIntegrand K S μv P W Y η r j := by
  unfold rowBallDualIntegrand
  simp only [probeOriginalCorrelationOrbitWeight_mk]
  exact sum_weighted_originalFullCorrelation_eq_gcd_mobius_chart K SF P.arithmetic
    (additiveGramIdealSupport K SF W Y) (additiveGramIdealSupport K SF W Y)
    (rowBallDualSpectralCoefficient K S μv P W Y η r (Quotient.mk _ j)) j

/-- The complete chart sum inherits the original orbit descent. This does
not assert that an individual artificial residual term is invariant. -/
theorem rowBallDualChartIntegrand_eq_of_mk_eq (P : ProbeData K SF)
    (W : SmoothAnnularTest) (Y η : ℝ) (r : {r : ℝ // 0 < r}) (j k : NZ)
    (h : (Quotient.mk _ j : OQ) = Quotient.mk _ k) :
    rowBallDualChartIntegrand K S μv P W Y η r j =
      rowBallDualChartIntegrand K S μv P W Y η r k := by
  rw [← rowBallDualIntegrand_mk_eq_chart K S μv P W Y η r j,
    ← rowBallDualIntegrand_mk_eq_chart K S μv P W Y η r k, h]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]

include μf in
/-- Actual finite periodic Fourier coefficients give their own bound and
absolute orbital unfolding; no summability premise is introduced. -/
theorem summable_rowBallDualPair (P : ProbeData K SF) (I J : E)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun q : OQ => probeOriginalCorrelationOrbitWeight K S P I J q *
      rowBallDualPairProfile K S μv P I J r q) := by
  let u := probeGenerator K SF P.arithmetic I
  let v := probeGenerator K SF P.arithmetic J
  let c := u.val * v.val
  have hc : c ≠ 0 := mul_ne_zero u.property v.property
  have hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S μf μv (rowBallFiniteFamily K S 1)
    (rowBallFiniteFamily_locallyConstant K S 1)
    (rowBallFiniteFamily_compactSupport K S 1)
  have hs := (hasSum_sIntegerPeriodicOrbitalProfile K SF Γ
    (traceSchwartzFourier K (rowBallArchTest K S 1))
    (sIntegerFiniteFourierTestFunction K S μv (rowBallFiniteFamily K S 1))
    hhat.1.continuous hhat.2 (additiveGramPairDualRadius K S P I J r) c hc
    (sIntegerPeriodicDivisorFourier K SF P.arithmetic.different_outside c hc
      (probeNegativeGaussPairResidue K SF P I J) 1)
    (sIntegerPeriodicDivisorFourier_literal_invariant K SF
      P.arithmetic.different_outside Γ c hc
      (probeNegativeGaussPairResidue K SF P I J)
      (probeNegativeGaussPairResidue_literal_invariant K SF P I J) 1)).summable
  simpa only [probeOriginalCorrelationOrbitWeight,
    sIntegerPeriodicFourierOrbitWeight, rowBallDualPairProfile, mul_assoc,
    c, u, v] using hs.mul_left (probePairOrbitCard K S P I J)⁻¹

include μf in
/-- The finite ideal-pair integrand is truly summable on the original
sixth-unit quotient, despite its pair-dependent dual radii. -/
theorem summable_rowBallDualIntegrand (P : ProbeData K SF)
    (W : SmoothAnnularTest) (Y η : ℝ) (r : {r : ℝ // 0 < r}) :
    Summable (rowBallDualIntegrand K S μv P W Y η r) := by
  unfold rowBallDualIntegrand
  apply summable_sum
  intro I _hI
  apply summable_sum
  intro J _hJ
  apply ((summable_rowBallDualPair K S μv μf P I J r).mul_left
    (actualAdditiveGramPairCoefficient K SF (fun _ => 1) W Y η I J)).congr
  intro q
  dsimp only [rowBallDualSpectralCoefficient]
  ring

include μf in
/-- The original row-ball nonzero dual is this summable integrand, with
the exact discriminant and radius/Y prefactor retained. -/
theorem rowBallDualSeriesTerm_one_eq_tsum (P : ProbeData K SF)
    (W : SmoothAnnularTest) (Y η : ℝ) (r : {r : ℝ // 0 < r}) :
    rowBallDualSeriesTerm K S μv P (fun _ => 1) W Y η r =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        ∑' q : OQ, rowBallDualIntegrand K S μv P W Y η r q := by
  have hrow (I J : E) :=
    ((summable_rowBallDualPair K S μv μf P I J r).mul_left
      (actualAdditiveGramPairCoefficient K SF (fun _ => 1) W Y η I J))
  have hexchange :
      (∑' q : OQ, ∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF (fun _ => 1) W Y η I J *
            (probeOriginalCorrelationOrbitWeight K S P I J q *
              rowBallDualPairProfile K S μv P I J r q)) =
      ∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF (fun _ => 1) W Y η I J *
            freeAdditiveGramPairDualOrbitalSeries K S μv P I J
              (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) r := by
    rw [Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
      (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
        (fun J _hJ => hrow I J))]
    apply Finset.sum_congr rfl
    intro I _hI
    rw [Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
      (fun J _hJ => hrow I J)]
    apply Finset.sum_congr rfl
    intro J _hJ
    simp only [tsum_mul_left, freeAdditiveGramPairDualOrbitalSeries,
      sIntegerWeightedOrbitalSeries, rowBallDualPairProfile]
  unfold rowBallDualSeriesTerm
  rw [← hexchange]
  congr 1
  apply tsum_congr
  intro q
  unfold rowBallDualIntegrand rowBallDualSpectralCoefficient
  apply Finset.sum_congr rfl
  intro I _hI
  apply Finset.sum_congr rfl
  intro J _hJ
  ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualChartDraft
