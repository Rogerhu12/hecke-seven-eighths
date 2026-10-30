import HeckeGeneral.Bridge.SIntegerDualSupport
import FLTReuse.M8531b1869d254748
import FLTReuse.Md9bb0dc096ff8cbe
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Full S-integer Poisson sums for S containing the actual different support.
The standard character, local Haar factors, and discriminant normalization
are retained. Both sums include their zero frequency. -/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier
  NumberField.StandardAddChar HeckeGeneral.Characters MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The genuine product of archimedean and normalized S-local Fourier factors
evaluated at a principal frequency. -/
def sIntegerDualTensorTerm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) (a : K) : ℂ :=
  let w := algebraMap K (AdeleRing (𝓞 K) K) a
  fourierIntegral (standardMixedAddCharacter K) volume φ
      (InfiniteAdeleRing.ringEquiv_mixedSpace K w.1) *
    sIntegerLocalFourierProduct K μv S h w.2

/-- Literal reindexing by the actual S-integer support, independent of
summability. No zero frequency is removed. -/
theorem tsum_sIntegerDualTensorTerm_eq_tsum_supported
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
      sIntegerDualTensorTerm K μv S φ h a.val) =
    ∑' a : K,
      let w := algebraMap K (AdeleRing (𝓞 K) K) a
      fourierIntegral (standardMixedAddCharacter K) volume φ
          (InfiniteAdeleRing.ringEquiv_mixedSpace K w.1) *
        (sIntegerLocalFourierProduct K μv S h w.2 *
          (if outsideSStandardAnnihilator K S w.2 then 1 else 0)) := by
  change (∑' a : {a : K // a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K},
    sIntegerDualTensorTerm K μv S φ h a.val) = _
  calc
    _ = ∑' a : K,
        ({a : K | a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K}).indicator
          (sIntegerDualTensorTerm K μv S φ h) a := tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro a
      have ha := outsideSStandardAnnihilator_principal_iff_sInteger K S hS a
      change _ = _ * (_ * (if outsideSStandardAnnihilator K S
        (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) then 1 else 0))
      rw [ha]
      by_cases hm : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K
      · have hm' : a ∈ {a : K | a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K} := hm
        rw [Set.indicator_of_mem hm', ite_eq_left hm, mul_one]
        rfl
      · have hm' : a ∉ {a : K | a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K} := hm
        rw [Set.indicator_of_notMem hm', ite_eq_right hm, mul_zero, mul_zero]

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ

/-- Genuine full Poisson summation with both sums over the same S-integer
ring, after S has absorbed the finitely many different primes. -/
theorem sIntegerSelfDualPoisson
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    (∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
      sIntegerTensorTerm K S φ h a.val) =
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      ∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
        sIntegerDualTensorTerm K μv S φ h a.val := by
  rw [tsum_sIntegerDualTensorTerm_eq_tsum_supported K μv S hS φ h]
  exact sIntegerLocalPoisson K ν μv μ S φ h hlc hcs

omit ν μ in
/-- The discriminant normalization is nonzero for every number field. -/
theorem sIntegerDiscriminantFactor_ne_zero :
    ((((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
      Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply div_ne_zero (pow_ne_zero _ (by norm_num))
  exact ne_of_gt (Real.sqrt_pos_of_pos
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))

/-- Absolute convergence of the actual dual S-integer sum follows from the
Schwartz--Bruhat Fourier preservation theorem and principal-lattice summability. -/
theorem summable_sIntegerDualTensorTerm
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    Summable fun a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K =>
      sIntegerDualTensorTerm K μv S φ h a.val := by
  have hF := fourierIntegral_mem_schwartzBruhat K μ (isGlobalAddChar_stdAddChar K)
    (sIntegerAdelicTestFunction_mem_schwartzBruhat K S φ h hlc hcs)
  have hs : Summable fun a : K =>
      fourierIntegral (stdAddChar K) μ (sIntegerAdelicTestFunction K S φ h)
        (algebraMap K (AdeleRing (𝓞 K) K) a) := by
    simpa only [zero_add] using summable_translate_of_mem_schwartzBruhat K hF 0
  have hn := (hs.subtype (fun a : K =>
    a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)).mul_left
      (((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹)
  have hp : Summable fun a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K =>
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
        Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        sIntegerDualTensorTerm K μv S φ h a.val := by
    apply hn.congr
    intro a
    have he := sIntegerAdelicTestFunction_fourier_factorization K ν μv μ S φ h hlc hcs
      (algebraMap K (AdeleRing (𝓞 K) K) a.val)
    have ha := (outsideSStandardAnnihilator_principal_iff_sInteger K S hS a.val).mpr
      a.property
    change outsideSStandardAnnihilator K S
      (algebraMap K (AdeleRing (𝓞 K) K) a.val).2 at ha
    simpa only [ha, ite_true, mul_one, sIntegerDualTensorTerm, Function.comp_apply] using he
  exact (summable_mul_left_iff (sIntegerDiscriminantFactor_ne_zero K)).mp hp

omit ν μ in
/-- Splitting off a single term uses proved summability, and keeps the
remaining indices as an explicit nonzero subtype. -/
theorem tsum_eq_zero_add_tsum_ne_zero {A : Type*} [Zero A]
    (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) = f 0 + ∑' a : {a : A // a ≠ 0}, f a.val := by
  rw [hf.tsum_eq_add_tsum_ite 0]
  congr 1
  calc
    _ = ∑' a : A, ({a : A | a ≠ 0}).indicator f a := by
      apply tsum_congr
      intro a
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]
    _ = _ := (tsum_subtype _ _).symm

/-- Both zero terms are explicit and retain their actual test-function
values; no value for either zero term is postulated. -/
theorem sIntegerSelfDualPoisson_nonzero
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    (∑' a : {a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K // a ≠ 0},
      sIntegerTensorTerm K S φ h a.val.val) =
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      (∑' a : {a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K // a ≠ 0},
        sIntegerDualTensorTerm K μv S φ h a.val.val) +
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        sIntegerDualTensorTerm K μv S φ h 0 - sIntegerTensorTerm K S φ h 0 := by
  have he := sIntegerSelfDualPoisson K ν μv μ S hS φ h hlc hcs
  rw [tsum_eq_zero_add_tsum_ne_zero _ (summable_sIntegerTensorTerm K S φ h hlc hcs),
    tsum_eq_zero_add_tsum_ne_zero _
      (summable_sIntegerDualTensorTerm K ν μv μ S hS φ h hlc hcs)] at he
  change sIntegerTensorTerm K S φ h 0 + _ =
    _ * (sIntegerDualTensorTerm K μv S φ h 0 + _) at he
  linear_combination he

end HeckeGeneral.Bridge
