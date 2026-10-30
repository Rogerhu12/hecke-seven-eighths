import HeckeGeneral.Bridge.SLocalSchwartzModel
import HeckeGeneral.Bridge.SIntegerFourierFactorization
import HeckeGeneral.Arithmetic.TraceLatticeCovolume
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import FLTReuse.Mfdd944592cac5200

/-!
# The standard trace Fourier transform in weighted Euclidean coordinates

The positive standard additive character is evaluated at `-(x*y)` in the
Fourier integral. In the weighted trace Euclidean coordinates its pairing is
`inner x (traceConjugation y)`. The mixed Lebesgue measure contributes the
factor `2^(-r₂)`, since `traceToMixed` divides every complex coordinate by
`sqrt 2`. Thus neither the complex conjugation nor the Jacobian is suppressed.

The resulting functions are actual Schwartz maps, constructed from Mathlib's
Schwartz Fourier transform and continuous linear coordinate changes.
Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField NumberField.InfinitePlace HeckeGeneral.Arithmetic
  MeasureTheory NumberField.AdelicFourier
open scoped Classical BigOperators FourierTransform ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

/-- The Jacobian is for the actual mixed Lebesgue measure, rather than a
self-dual trace normalization. -/
theorem map_traceToMixed_volume :
    Measure.map (traceToMixed K)
        (volume : Measure (mixedEmbedding.euclidean.mixedSpace K)) =
      ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) •
        (volume : Measure (mixedEmbedding.mixedSpace K)) := by
  have hmap : Measure.map (traceMixedUnscale K)
      (volume : Measure (mixedEmbedding.mixedSpace K)) =
      ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) • volume := by
    ext s hs
    rw [Measure.map_apply (traceMixedUnscale K).continuous.measurable hs,
      Measure.smul_apply, smul_eq_mul,
      Measure.addHaar_preimage_continuousLinearEquiv,
      det_traceMixedUnscale_symm,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  change Measure.map
    ((traceMixedUnscale K) ∘ (mixedEmbedding.euclidean.toMixed K)) volume = _
  rw [← Measure.map_map (traceMixedUnscale K).continuous.measurable
      (mixedEmbedding.euclidean.toMixed K).continuous.measurable,
    (mixedEmbedding.euclidean.volumePreserving_toMixed K).map_eq, hmap]

/-- Bochner change of variables with the actual positive Jacobian. This
identity also respects Mathlib's totalized integral for nonintegrable functions. -/
theorem integral_comp_traceToMixed
    (f : mixedEmbedding.mixedSpace K → ℂ) :
    (∫ x : mixedEmbedding.euclidean.mixedSpace K, f (traceToMixed K x)) =
      ((2 : ℝ) ^ nrComplexPlaces K) •
        (∫ y : mixedEmbedding.mixedSpace K, f y) := by
  have he : MeasurableEmbedding (traceToMixed K) :=
    (traceToMixed K).toHomeomorph.measurableEmbedding
  rw [← he.integral_map f, map_traceToMixed_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]

/-- Mixed integration in weighted trace coordinates has the inverse Jacobian. -/
theorem integral_eq_inv_jacobian_traceToMixed
    (f : mixedEmbedding.mixedSpace K → ℂ) :
    (∫ y : mixedEmbedding.mixedSpace K, f y) =
      ((((2 : ℝ) ^ nrComplexPlaces K)⁻¹ : ℝ) : ℂ) *
        (∫ x : mixedEmbedding.euclidean.mixedSpace K, f (traceToMixed K x)) := by
  rw [integral_comp_traceToMixed, Complex.real_smul]
  push_cast
  have hc : (2 : ℂ) ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The trace pairing in the weighted coordinates requires conjugation of
the second Euclidean argument, including at every complex place. -/
theorem trace_mul_traceToMixed
    (x y : mixedEmbedding.euclidean.mixedSpace K) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace K)
        (traceToMixed K x * traceToMixed K y) =
      inner ℝ x (traceConjugation K y) := by
  let a := mixedEmbedding.euclidean.toMixed K x
  let b := mixedEmbedding.euclidean.toMixed K y
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hcoef : (2 : ℝ) * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) = 1 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [hsqrt]
    nlinarith
  have hcomplex (z w : ℂ) :
      2 * (((Real.sqrt 2)⁻¹ • z) * ((Real.sqrt 2)⁻¹ • w)).re =
        z.re * w.re - z.im * w.im := by
    calc
      _ = (2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹)) * (z * w).re := by
        simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
        ring
      _ = _ := by rw [hcoef, one_mul, Complex.mul_re]
  rw [mixedEmbedding.trace_mixedSpace_apply]
  have hinner : inner ℝ x (traceConjugation K y) =
      (∑ v : {v : InfinitePlace K // v.IsReal}, b.1 v * a.1 v) +
        ((∑ v : {v : InfinitePlace K // v.IsComplex}, (b.2 v).re * (a.2 v).re) -
          ∑ v : {v : InfinitePlace K // v.IsComplex}, (b.2 v).im * (a.2 v).im) := by
    simp [a, b, traceConjugation, mixedEmbedding.euclidean.toMixed,
      WithLp.prod_inner_apply, PiLp.inner_apply, Finset.sum_sub_distrib,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  rw [hinner]
  change (∑ v : {v : InfinitePlace K // v.IsReal}, a.1 v * b.1 v) +
      (∑ v : {v : InfinitePlace K // v.IsComplex},
        2 * (((Real.sqrt 2)⁻¹ • a.2 v) * ((Real.sqrt 2)⁻¹ • b.2 v)).re) = _
  simp_rw [hcomplex, Finset.sum_sub_distrib]
  simp only [mul_comm]

/-- The actual positive standard character has the Euclidean trace kernel
after the change of variables. The Fourier convention supplies the minus sign. -/
theorem standardMixedAddCharacter_neg_mul_traceToMixed
    (x y : mixedEmbedding.euclidean.mixedSpace K) :
    standardMixedAddCharacter K (-(traceToMixed K x * traceToMixed K y)) =
      (Real.fourierChar (-(inner ℝ x (traceConjugation K y))) : ℂ) := by
  rw [standardMixedAddCharacter_apply, map_neg, trace_mul_traceToMixed]

/-- An explicit Schwartz map for the trace Fourier transform pulled back to
the weighted Euclidean space. This uses the proved Mathlib Schwartz Fourier
transform, not a Schwartz-preservation hypothesis. -/
def traceSchwartzFourier
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ :=
  (((((2 : ℝ) ^ nrComplexPlaces K)⁻¹ : ℝ) : ℂ)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (traceConjugation K).toContinuousLinearEquiv (𝓕 φ)

@[simp] theorem traceSchwartzFourier_apply
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (y : mixedEmbedding.euclidean.mixedSpace K) :
    traceSchwartzFourier K φ y =
      ((((2 : ℝ) ^ nrComplexPlaces K)⁻¹ : ℝ) : ℂ) *
        (𝓕 (φ : mixedEmbedding.euclidean.mixedSpace K → ℂ)) (traceConjugation K y) := rfl

/-- Exact Fourier identity, with both complex conjugation and inverse Jacobian. -/
theorem fourierIntegral_traceSchwartzToMixed_traceToMixed
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (y : mixedEmbedding.euclidean.mixedSpace K) :
    fourierIntegral (standardMixedAddCharacter K) volume (traceSchwartzToMixed K φ)
        (traceToMixed K y) = traceSchwartzFourier K φ y := by
  rw [fourierIntegral_def, integral_eq_inv_jacobian_traceToMixed,
    traceSchwartzFourier_apply, Real.fourier_eq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [standardMixedAddCharacter_neg_mul_traceToMixed,
      traceSchwartzToMixed_apply, ContinuousLinearEquiv.symm_apply_apply]
    simp only [Circle.smul_def, smul_eq_mul]

/-- The mixed-space Fourier transform itself as an actual Schwartz map. -/
def mixedTraceSchwartzFourier
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    SchwartzMap (mixedEmbedding.mixedSpace K) ℂ :=
  traceSchwartzToMixed K (traceSchwartzFourier K φ)

/-- Every mixed-space frequency is covered, without any lattice or ideal restriction. -/
theorem mixedTraceSchwartzFourier_apply
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (y : mixedEmbedding.mixedSpace K) :
    mixedTraceSchwartzFourier K φ y =
      fourierIntegral (standardMixedAddCharacter K) volume (traceSchwartzToMixed K φ) y := by
  change traceSchwartzFourier K φ ((traceToMixed K).symm y) = _
  rw [← fourierIntegral_traceSchwartzToMixed_traceToMixed,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The requested pullback is exactly the constructed Euclidean Schwartz map. -/
theorem traceSchwartzFourier_eq_pullback
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    (traceSchwartzFourier K φ : mixedEmbedding.euclidean.mixedSpace K → ℂ) =
      fun y => fourierIntegral (standardMixedAddCharacter K) volume
        (traceSchwartzToMixed K φ) (traceToMixed K y) := by
  funext y
  exact (fourierIntegral_traceSchwartzToMixed_traceToMixed K φ y).symm

end HeckeGeneral.Bridge
