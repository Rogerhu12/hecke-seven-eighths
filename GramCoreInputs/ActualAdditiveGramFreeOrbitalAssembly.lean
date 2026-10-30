import ActualAdditiveGramOrbitalAssembly
import ActualGramCompactShapeMajorant

/-!
UNCOMPILED / native 0. Actual Am-square orbital Poisson for an INDEPENDENT
archimedean Schwartz test and a finite locally constant compact tensor. The
probe supplies only its arithmetic Gauss coefficients in this assembly;
P.additive is not used as the orbital test. Genuine periodic Haar unfolding
proves convergence before the finite ideal-pair exchange. The discriminant,
actual covolume, true pair dual radius and BOTH zero contributions remain.
No Gram estimate, summability or finite-ray coefficient shape is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramFreeDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualProbeGaussFourierDraft ActualProbePairFourierDraft ActualProbePairOrbitalDraft
open ActualGramMajorantDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SF K
local notation "Γ" => sixthPowerUnits K SF
local notation "OQ" => SIntegerOrbits K SF Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Af" => gramFiniteAdditiveSpace K S

local instance free_originalSixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- A free orbital profile, independent of P.additive and allowed to be
nonzero at the additive origin. The original Gamma and its norm are retained. -/
def freeAdditiveGramOrbitProfile (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) (q : OQ) : ℂ :=
  sUnitOrbitalProfile K SF
    (sLocalTensorTestFunction K SF φ (sIntegerFiniteTestFunction K S h))
    ⟨r.val * (sIntegerOrbitNorm K SF Γ q).val,
      mul_pos r.property (sIntegerOrbitNorm K SF Γ q).property⟩

/-- The actual negative Gauss pair supplies a finite periodic coefficient;
proved absolute Haar unfolding supplies summability for the free test. -/
theorem summable_probeNegativeGaussPair_freeOrbitalProfile
    (P : ProbeData K SF) (I J : ExteriorIdeal K SF)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    Summable (fun q : OQ => probeNegativeGaussPairOrbitWeight K S P I J q *
      freeAdditiveGramOrbitProfile K S φ h r q) := by
  have hs := hasSum_sIntegerPeriodicOrbitalProfile K SF Γ φ
    (sIntegerFiniteTestFunction K S h)
    (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) r
    ((probeGenerator K SF P.arithmetic I).val * (probeGenerator K SF P.arithmetic J).val)
    (mul_ne_zero (probeGenerator K SF P.arithmetic I).property
      (probeGenerator K SF P.arithmetic J).property)
    (probeNegativeGaussPairResidue K SF P I J)
    (probeNegativeGaussPairResidue_literal_invariant K SF P I J)
  simpa only [probeNegativeGaussPairOrbitWeight, freeAdditiveGramOrbitProfile] using hs.summable

/-- Actual Am square times a free orbital profile is summable. No estimate
for Am, no majorant positivity and no convergence premise is an input. -/
theorem summable_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    Summable (fun q : OQ =>
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        freeAdditiveGramOrbitProfile K S φ h r q) := by
  have hrow (I J : ExteriorIdeal K SF) :=
    (summable_probeNegativeGaussPair_freeOrbitalProfile K S P I J φ h hlc hcs r).mul_left
      (actualAdditiveGramPairCoefficient K SF c W Y η I J)
  have hs := summable_sum (s := additiveGramIdealSupport K SF W Y)
    (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
      (fun J _hJ => hrow I J))
  apply (hs.mul_left ((Y ^ (-3 : ℝ) : ℝ) : ℂ)).congr
  intro q
  symm
  rw [actualAdditiveGramOrbitAmplitude_norm_sq_eq_double_sum K S P c W Y η hY q]
  simp only [Finset.sum_mul, mul_assoc]

/-- Genuine convergence permits finite ideal-pair exchange for the free test. -/
theorem tsum_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    (∑' q : OQ,
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        freeAdditiveGramOrbitProfile K S φ h r q) =
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
                (probeNegativeGaussPairOrbitWeight K S P I J) := by
  have hrow (I J : ExteriorIdeal K SF) :=
    (summable_probeNegativeGaussPair_freeOrbitalProfile K S P I J φ h hlc hcs r).mul_left
      (actualAdditiveGramPairCoefficient K SF c W Y η I J)
  calc
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ∑' q : OQ,
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              (probeNegativeGaussPairOrbitWeight K S P I J q *
                freeAdditiveGramOrbitProfile K S φ h r q) := by
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
                freeAdditiveGramOrbitProfile K S φ h r q) := by
      congr 1
      rw [Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
        (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
          (fun J _hJ => hrow I J))]
      apply Finset.sum_congr rfl
      intro I _hI
      exact Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
        (fun J _hJ => hrow I J)
    _ = _ := by
      simp only [tsum_mul_left, sIntegerWeightedOrbitalSeries, freeAdditiveGramOrbitProfile]

/-- The actual chosen compact-shape majorant is a direct free-test instance.
It is not converted into an annular AdditiveProbeTest. -/
theorem summable_compactShapeMajorant_actualAm_freeProfile
    (C : Set (V × Af)) (hC : IsCompact C)
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    Summable (fun q : OQ =>
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        freeAdditiveGramOrbitProfile K S (compactShapeArchTest K S C hC)
          (compactShapeFiniteFamily K S C hC) r q) :=
  summable_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile K S P c W Y η hY
    (compactShapeArchTest K S C hC) (compactShapeFiniteFamily K S C hC)
    (compactShapeFiniteFamily_locallyConstant K S C hC)
    (compactShapeFiniteFamily_compactSupport K S C hC) r

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- True pair dual radius and original full correlation, with the free tests. -/
def freeAdditiveGramPairDualOrbitalSeries (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
    (sIntegerFiniteFourierTestFunction K S μv h)
    (additiveGramPairDualRadius K S P I J r)
    (probeOriginalCorrelationOrbitWeight K S P I J)

/-- BOTH actual zero terms. The free test may equal one at zero, so the
original negative Gauss zero contribution is retained explicitly. -/
def freeAdditiveGramPairZeroCorrection (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) : ℂ :=
  ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
      (additiveGramFullCorrelation K S P I J 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
    (probeGauss K SF P I 0 * conj (probeGauss K SF P J 0)) *
      sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0

include μ μf in
/-- The GENUINE generic pair formula, not the P.additive specialization. -/
theorem freeAdditiveGramPair_orbital_poisson (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
      (probeNegativeGaussPairOrbitWeight K S P I J) =
    ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
      freeAdditiveGramPairDualOrbitalSeries K S μv P I J φ h r +
    ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
      freeAdditiveGramPairZeroCorrection K S μv P I J φ h r := by
  simpa only [freeAdditiveGramPairDualOrbitalSeries, freeAdditiveGramPairZeroCorrection,
    additiveGramPairDualRadius, additiveGramPairModulus, additiveGramFullCorrelation,
    additiveGramPoissonFieldFactor] using
    probeGauss_pair_orbital_poisson (K := K) (S := S) (P := P) (I := I) (J := J)
      (ν := μf) (μv := μv) (μ := μ) φ h hlc hcs r

include μ μf in
/-- Full actual Am-square orbital assembly for independent free tests.
Convergence and the finite exchange are proved before generic Poisson is used. -/
theorem tsum_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile_poisson
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    (∑' q : OQ,
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        freeAdditiveGramOrbitProfile K S φ h r q) =
    ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
      (∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I J *
            freeAdditiveGramPairDualOrbitalSeries K S μv P I J φ h r) +
    (((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
      (∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I J *
            freeAdditiveGramPairZeroCorrection K S μv P I J φ h r) := by
  rewrite [tsum_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile
    K S P c W Y η hY φ h hlc hcs r]
  have hp (I J : ExteriorIdeal K SF) :=
    freeAdditiveGramPair_orbital_poisson K S μf μv μ P I J φ h hlc hcs r
  simp_rw [hp]
  have hterm (I J : ExteriorIdeal K SF) :
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (actualAdditiveGramPairCoefficient K SF c W Y η I J *
          (((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
            freeAdditiveGramPairDualOrbitalSeries K S μv P I J φ h r +
          ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
            freeAdditiveGramPairZeroCorrection K S μv P I J φ h r)) =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        (actualAdditiveGramPairCoefficient K SF c W Y η I J *
          freeAdditiveGramPairDualOrbitalSeries K S μv P I J φ h r) +
      (((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
        (actualAdditiveGramPairCoefficient K SF c W Y η I J *
          freeAdditiveGramPairZeroCorrection K S μv P I J φ h r) := by ring
  simp only [Finset.mul_sum]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]

include μ μf in
/-- Direct consumer of the constructed compact-shape tests. No lower bound
for their orbital profile is used or assumed by this exact identity. -/
theorem compactShapeMajorant_actualAm_free_orbital_poisson
    (C : Set (V × Af)) (hC : IsCompact C)
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    let φ := compactShapeArchTest K S C hC
    let h := compactShapeFiniteFamily K S C hC
    (∑' q : OQ,
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        freeAdditiveGramOrbitProfile K S φ h r q) =
    ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
      (∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I J *
            freeAdditiveGramPairDualOrbitalSeries K S μv P I J φ h r) +
    (((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
      (∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I J *
            freeAdditiveGramPairZeroCorrection K S μv P I J φ h r) := by
  exact tsum_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile_poisson K S μf μv μ
    P c W Y η hY (compactShapeArchTest K S C hC) (compactShapeFiniteFamily K S C hC)
    (compactShapeFiniteFamily_locallyConstant K S C hC)
    (compactShapeFiniteFamily_compactSupport K S C hC) r

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramFreeDraft
