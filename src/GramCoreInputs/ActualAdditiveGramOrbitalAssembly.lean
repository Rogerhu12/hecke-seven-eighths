import ActualAdditiveGramPoissonAssembly
import ActualProbePairOrbitalPoisson

/-!
UNCOMPILED / native 0. The literal Am square on the ORIGINAL sixth-unit
orbits is expanded into its actual finite ideal-pair sum. Each periodic
orbital row is genuinely summable by the proved absolute Haar unfolding.
Finite exchange then consumes the actual orbital Poisson identity. Both
zero terms, the actual Haar covolume and the discriminant remain explicit.
No summability, Gram estimate or finite-ray form of c is an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft
open ActualProbePairPoissonDraft ActualProbePairOrbitalDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SF K
local notation "Γ" => sixthPowerUnits K SF
local notation "OQ" => SIntegerOrbits K SF Γ

local instance originalSixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

/-- The original finite ideal envelope works simultaneously on every orbit. -/
theorem actualAdditiveGramOrbitAmplitude_norm_sq_eq_double_sum
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (q : OQ) :
    ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) =
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              probeNegativeGaussPairOrbitWeight K S P I J q := by
  refine Quotient.inductionOn q ?_
  intro m
  simpa only [actualAdditiveGramOrbitAmplitude_mk,
    probeNegativeGaussPairOrbitWeight_mk, probeNegativeGaussPairResidue_mk] using
    actualAdditiveGramAmplitude_norm_sq_eq_residue_double_sum K SF P c W Y η hY m.val

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The same original radial profile for all ideal pairs. -/
def additiveGramOrbitProfile (P : ProbeData K SF) (r : {r : ℝ // 0 < r})
    (q : OQ) : ℂ :=
  sUnitOrbitalProfile K SF
    (sLocalTensorTestFunction K SF P.additive.infiniteTest
      (fun y => ∏ v : SF, P.additive.finiteTest v (y v)))
    ⟨r.val * (sIntegerOrbitNorm K SF Γ q).val,
      mul_pos r.property (sIntegerOrbitNorm K SF Γ q).property⟩

/-- Actual periodic Haar unfolding proves convergence; no bound on the
Gauss pair or convergence statement is supplied as a hypothesis. -/
theorem summable_probeNegativeGaussPair_orbitalProfile
    (P : ProbeData K SF) (I J : ExteriorIdeal K SF) (r : {r : ℝ // 0 < r}) :
    Summable (fun q : OQ => probeNegativeGaussPairOrbitWeight K S P I J q *
      additiveGramOrbitProfile K S P r q) := by
  have hs := hasSum_sIntegerPeriodicOrbitalProfile K SF Γ
    P.additive.infiniteTest (sIntegerFiniteTestFunction K S (probeFiniteFamily K S P))
    (continuous_sIntegerFiniteTestFunction K S (probeFiniteFamily K S P)
      (probeFiniteFamily_locallyConstant K S P))
    (hasCompactSupport_sIntegerFiniteTestFunction K S (probeFiniteFamily K S P)
      (probeFiniteFamily_compactSupport K S P)) r
    ((probeGenerator K SF P.arithmetic I).val * (probeGenerator K SF P.arithmetic J).val)
    (mul_ne_zero (probeGenerator K SF P.arithmetic I).property
      (probeGenerator K SF P.arithmetic J).property)
    (probeNegativeGaussPairResidue K SF P I J)
    (probeNegativeGaussPairResidue_literal_invariant K SF P I J)
  simpa only [probeNegativeGaussPairOrbitWeight, additiveGramOrbitProfile,
    probeFiniteTestFunction_eq] using hs.summable

/-- The literal orbit Am square, multiplied by its original radial profile,
is summable for every positive radius. -/
theorem summable_actualAdditiveGramOrbitAmplitude_norm_sq_profile
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    Summable (fun q : OQ =>
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        additiveGramOrbitProfile K S P r q) := by
  have hrow (I J : ExteriorIdeal K SF) :=
    (summable_probeNegativeGaussPair_orbitalProfile K S P I J r).mul_left
      (actualAdditiveGramPairCoefficient K SF c W Y η I J)
  have hs := summable_sum (s := additiveGramIdealSupport K SF W Y)
    (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
      (fun J _hJ => hrow I J))
  apply (hs.mul_left ((Y ^ (-3 : ℝ) : ℝ) : ℂ)).congr
  intro q
  symm
  rw [actualAdditiveGramOrbitAmplitude_norm_sq_eq_double_sum K S P c W Y η hY q]
  simp only [Finset.sum_mul, mul_assoc]

/-- Exchange the genuine convergent orbital series with the actual finite
ideal-pair expansion, before applying Poisson. -/
theorem tsum_actualAdditiveGramOrbitAmplitude_norm_sq_profile
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    (∑' q : OQ,
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        additiveGramOrbitProfile K S P r q) =
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              sIntegerWeightedOrbitalSeries K S Γ P.additive.infiniteTest
                (fun y => ∏ v : SF, P.additive.finiteTest v (y v)) r
                (probeNegativeGaussPairOrbitWeight K S P I J) := by
  have hrow (I J : ExteriorIdeal K SF) :=
    (summable_probeNegativeGaussPair_orbitalProfile K S P I J r).mul_left
      (actualAdditiveGramPairCoefficient K SF c W Y η I J)
  calc
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ∑' q : OQ,
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              (probeNegativeGaussPairOrbitWeight K S P I J q *
                additiveGramOrbitProfile K S P r q) := by
      rewrite [← tsum_mul_left]
      apply tsum_congr
      intro q
      rw [actualAdditiveGramOrbitAmplitude_norm_sq_eq_double_sum K S P c W Y η hY q]
      simp only [Finset.sum_mul, mul_assoc]
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            ∑' q : OQ, actualAdditiveGramPairCoefficient K SF c W Y η I J *
              (probeNegativeGaussPairOrbitWeight K S P I J q *
                additiveGramOrbitProfile K S P r q) := by
      congr 1
      rw [Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
        (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
          (fun J _hJ => hrow I J))]
      apply Finset.sum_congr rfl
      intro I _hI
      exact Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
        (fun J _hJ => hrow I J)
    _ = _ := by
      simp only [tsum_mul_left, sIntegerWeightedOrbitalSeries, additiveGramOrbitProfile]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- The common dual orbital profile with the true pair radius. -/
def additiveGramPairDualOrbitalSeries (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (r : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K P.additive.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S μv (probeFiniteFamily K S P))
    (additiveGramPairDualRadius K S P I J r)
    (probeOriginalCorrelationOrbitWeight K S P I J)

include μ μf in
/-- Actual orbital pair Poisson, retaining the complete Haar zero correction. -/
theorem additiveGramPair_orbital_poisson (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (r : {r : ℝ // 0 < r}) :
    sIntegerWeightedOrbitalSeries K S Γ P.additive.infiniteTest
      (fun y => ∏ v : SF, P.additive.finiteTest v (y v)) r
      (probeNegativeGaussPairOrbitWeight K S P I J) =
    ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
      additiveGramPairDualOrbitalSeries K S μv P I J r +
    ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
      additiveGramPairZeroCorrection K S μv P I J r := by
  simpa only [additiveGramPairDualOrbitalSeries, additiveGramPairDualRadius,
    additiveGramPairModulus, additiveGramPairZeroCorrection, additiveGramFullCorrelation,
    additiveGramPoissonFieldFactor] using
    probeGauss_pair_additive_orbital_poisson (K := K) (S := S) (P := P)
      (I := I) (J := J) (ν := μf) (μv := μv) (μ := μ) r

include μ μf in
/-- The original Am square on every original sixth-unit sector satisfies
orbital Poisson. No convergence or coefficient-shape hypothesis is added. -/
theorem tsum_actualAdditiveGramOrbitAmplitude_norm_sq_profile_poisson
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    (∑' q : OQ,
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        additiveGramOrbitProfile K S P r q) =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              additiveGramPairDualOrbitalSeries K S μv P I J r) +
      (((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              additiveGramPairZeroCorrection K S μv P I J r) := by
  rewrite [tsum_actualAdditiveGramOrbitAmplitude_norm_sq_profile K S P c W Y η hY r]
  have hp (I J : ExteriorIdeal K SF) := additiveGramPair_orbital_poisson K S μf μv μ P I J r
  simp_rw [hp]
  have hterm (I J : ExteriorIdeal K SF) :
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (actualAdditiveGramPairCoefficient K SF c W Y η I J *
          (((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
            additiveGramPairDualOrbitalSeries K S μv P I J r +
          ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
            additiveGramPairZeroCorrection K S μv P I J r)) =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        (actualAdditiveGramPairCoefficient K SF c W Y η I J *
          additiveGramPairDualOrbitalSeries K S μv P I J r) +
      (((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
        (actualAdditiveGramPairCoefficient K SF c W Y η I J *
          additiveGramPairZeroCorrection K S μv P I J r) := by ring
  simp only [Finset.mul_sum]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
