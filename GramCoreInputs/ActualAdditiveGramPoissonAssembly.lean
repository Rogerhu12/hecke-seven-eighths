import ActualAdditiveGramRowSummability

/-!
UNCOMPILED / native 0. The literal Am square row sum, with the same fixed
ideal coefficient c, is expanded and the actual P.additive pointwise Poisson
identity is applied to each ideal pair. The original full correlation,
true pair modulus, shifted inverse norm-one argument and both zero terms
remain explicit. At radius Q inverse the common dual prefactor is exactly
Q * Y^(-3) * D_K. No Gram bound or finite-ray shape of c is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft ActualProbePairPoissonDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SF K
local notation "NZ" => NonzeroRingElements OS
local notation "G" => sLocalMultiplicativeGroup K SF
local notation "T" => sLocalNormOneGroup K SF

/-- The actual field factor in the first trace Poisson formula. -/
def additiveGramPoissonFieldFactor : ℂ :=
  (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)

def additiveGramPairModulus (P : ProbeData K SF) (I J : ExteriorIdeal K SF) : NZ :=
  ⟨(probeGenerator K SF P.arithmetic I).val *
      (probeGenerator K SF P.arithmetic J).val,
    mul_ne_zero (probeGenerator K SF P.arithmetic I).property
      (probeGenerator K SF P.arithmetic J).property⟩

def additiveGramPairDualRadius (P : ProbeData K SF) (I J : ExteriorIdeal K SF)
    (r : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨(r.val * (sIntegerElementNorm K SF (additiveGramPairModulus K S P I J)).val)⁻¹,
    inv_pos.mpr (mul_pos r.property
      (sIntegerElementNorm K SF (additiveGramPairModulus K S P I J)).property)⟩

def additiveGramPairNormOneShift (P : ProbeData K SF) (I J : ExteriorIdeal K SF) : T :=
  sIntegerModulusNormOneShift K SF (additiveGramPairModulus K S P I J).val
    (additiveGramPairModulus K S P I J).property

/-- The full actual coefficient, including zero and nonunit frequencies. -/
def additiveGramFullCorrelation (P : ProbeData K SF) (I J : ExteriorIdeal K SF)
    (a : OS) : ℂ :=
  sIntegerSexticOriginalFullCorrelation K SF
    P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
    (probeArithmetic_six_support K SF P.arithmetic)
    (probeGenerator K SF P.arithmetic I) (probeGenerator K SF P.arithmetic J) a

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- Literal nonzero dual row series of the actual full correlation. -/
def additiveGramPairDualSeries (P : ProbeData K SF) (I J : ExteriorIdeal K SF)
    (r : {r : ℝ // 0 < r}) (x : T) : ℂ :=
  ∑' a : NZ, additiveGramFullCorrelation K S P I J a.val *
    sIntegerSchwartzTerm K SF (traceSchwartzFourier K P.additive.infiniteTest)
      (sIntegerFiniteFourierTestFunction K S μv (probeFiniteFamily K S P))
      (additiveGramPairDualRadius K S P I J r) a
      (additiveGramPairNormOneShift K S P I J * x⁻¹)

/-- The positive dual zero term minus the original negative Gauss zero term.
Neither term is removed using a support argument. -/
def additiveGramPairZeroCorrection (P : ProbeData K SF) (I J : ExteriorIdeal K SF)
    (r : {r : ℝ // 0 < r}) : ℂ :=
  ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
      (additiveGramFullCorrelation K S P I J 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K P.additive.infiniteTest)
          (probeFiniteFamily K S P) 0) -
    (probeGauss K SF P I 0 * conj (probeGauss K SF P J 0)) *
      sIntegerTensorTerm K S (traceSchwartzToMixed K P.additive.infiniteTest)
        (probeFiniteFamily K S P) 0

include μ μf in
/-- Repackage the actual pointwise Poisson endpoint without changing either
zero term, the pair modulus or the original test. -/
theorem tsum_probeNegativeGaussPair_mul_additiveTest_eq_dual
    (P : ProbeData K SF) (I J : ExteriorIdeal K SF)
    (r : {r : ℝ // 0 < r}) (x : T) :
    (∑' a : NZ,
      probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ a.val) *
        additiveTest K SF P.additive
          (sLocalNormSection K SF r * (x : G) * sLocalNonzeroIntegerDiagonal K SF a)) =
      ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
        additiveGramPairDualSeries K S μv P I J r x +
      additiveGramPairZeroCorrection K S μv P I J r := by
  simpa only [additiveGramPairDualSeries, additiveGramPairZeroCorrection,
    additiveGramFullCorrelation, additiveGramPairDualRadius,
    additiveGramPairNormOneShift, additiveGramPairModulus, additiveGramPoissonFieldFactor,
    probeNegativeGaussPairResidue_mk] using
    probeGauss_pair_additive_pointwise_poisson K S μf μv μ P I J r x

include μ μf in
/-- Actual Am square row sum equals a finite ideal-pair sum of actual dual
Schwartz series, together with both unchanged zero contributions. c is fixed
before Y and the spectral parameter; no ray shape or Gram estimate is assumed. -/
theorem tsum_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest_poisson
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) (x : T) :
    (∑' m : NZ,
      ((‖actualAdditiveGramAmplitude K SF P c W Y η m.val‖ ^ 2 : ℝ) : ℂ) *
        additiveTest K SF P.additive
          (sLocalNormSection K SF r * (x : G) * sLocalNonzeroIntegerDiagonal K SF m)) =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              additiveGramPairDualSeries K S μv P I J r x) +
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              additiveGramPairZeroCorrection K S μv P I J r) := by
  rewrite [tsum_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest K S
    P c W Y η hY (sLocalNormSection K SF r * (x : G))]
  have hp (I J : ExteriorIdeal K SF) :=
    tsum_probeNegativeGaussPair_mul_additiveTest_eq_dual K S μf μv μ P I J r x
  simp_rw [hp]
  have hterm (I J : ExteriorIdeal K SF) :
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
          (actualAdditiveGramPairCoefficient K SF c W Y η I J *
            (((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K) *
              additiveGramPairDualSeries K S μv P I J r x +
              additiveGramPairZeroCorrection K S μv P I J r)) =
        ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
          (actualAdditiveGramPairCoefficient K SF c W Y η I J *
            additiveGramPairDualSeries K S μv P I J r x) +
        ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
          (actualAdditiveGramPairCoefficient K SF c W Y η I J *
            additiveGramPairZeroCorrection K S μv P I J r) := by ring
  simp only [Finset.mul_sum]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]

include μ μf in
/-- At the original radius Q inverse, the common nonzero dual prefactor is
exactly Q * Y^(-3) * D_K. The zero correction retains its original full form. -/
theorem tsum_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest_poisson_inv
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (Q : ℝ) (hQ : 0 < Q) (x : T) :
    let r : {r : ℝ // 0 < r} := ⟨Q⁻¹, inv_pos.mpr hQ⟩
    (∑' m : NZ,
      ((‖actualAdditiveGramAmplitude K SF P c W Y η m.val‖ ^ 2 : ℝ) : ℂ) *
        additiveTest K SF P.additive
          (sLocalNormSection K SF r * (x : G) * sLocalNonzeroIntegerDiagonal K SF m)) =
      ((Q : ℂ) * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              additiveGramPairDualSeries K S μv P I J r x) +
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              additiveGramPairZeroCorrection K S μv P I J r) := by
  simpa only [Complex.ofReal_inv, inv_inv] using
    tsum_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest_poisson
      K S μf μv μ P c W Y η hY ⟨Q⁻¹, inv_pos.mpr hQ⟩ x

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
