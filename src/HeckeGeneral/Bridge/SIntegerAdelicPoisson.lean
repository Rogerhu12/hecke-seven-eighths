import FLTReuse.M791e48edf6c15dd6
import FLTReuse.M29d0733d9aaf5d27
import FLTReuse.M288314d062abd3e9
import FLTReuse.M0c8fe1e24b28af5e
import FLTReuse.M8a18b6fa749851ee
import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# S-integer summation from the actual adelic Poisson theorem

An archimedean Schwartz function and finitely many compactly supported locally
constant local functions give a genuine adelic Schwartz--Bruhat function by
putting the integer indicator at every other finite place. Its principal
evaluation vanishes outside the valuation-defined ring of S-integers.
The proved global Poisson formula therefore reindexes its left side by that
actual ring, with the original Haar normalization retained.

The right side here is the actual adelic Fourier integral. Identifying it with
a product of S-local transforms, and identifying its dual frequency support
with the localization of the inverse different, are separate bridges. In
particular this module does not replace the standard trace annihilator by the
integer lattice or silently normalize the adelic box to have measure one.

The imported general Poisson theorem has the explicit scope `K : Type`.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier MeasureTheory
open scoped Classical SchwartzMap Topology

variable (K : Type) [Field K] [NumberField K]

/-- Actual S-local data extended by the integral indicator outside S. -/
def sIntegerFiniteMask (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (x : FiniteAdeleRing (𝓞 K) K) : ℂ :=
  (∏ v ∈ S, h v (x v)) *
    if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      x v ∈ v.adicCompletionIntegers K then 1 else 0

/-- The compact finite adelic factor is proved from the actual local functions. -/
theorem sIntegerFiniteMask_locallyConstant_compactSupport
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (sIntegerFiniteMask K S h) ∧
      HasCompactSupport (sIntegerFiniteMask K S h) :=
  isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
    K S h hlc hcs

/-- An actual pure tensor on the full adelic ring, using its mixed embedding. -/
def sIntegerAdelicTestFunction (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (x : AdeleRing (𝓞 K) K) : ℂ :=
  φ (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * sIntegerFiniteMask K S h x.2

theorem sIntegerAdelicTestFunction_mem_pureTensorSet
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    sIntegerAdelicTestFunction K S φ h ∈ pureTensorSet K := by
  have hf := sIntegerFiniteMask_locallyConstant_compactSupport K S h hlc hcs
  exact tensor_mem_pureTensorSet φ (sIntegerFiniteMask K S h) hf.1 hf.2

theorem sIntegerAdelicTestFunction_mem_schwartzBruhat
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    sIntegerAdelicTestFunction K S φ h ∈ schwartzBruhat K :=
  mem_schwartzBruhat_of_mem_pureTensorSet
    (sIntegerAdelicTestFunction_mem_pureTensorSet K S φ h hlc hcs)

/-- Integral completion membership of a principal element is the defining
global valuation inequality, without a change of normalization. -/
theorem localIntegral_algebraMap_iff (v : HeightOneSpectrum (𝓞 K)) (a : K) :
    algebraMap K (v.adicCompletion K) a ∈ v.adicCompletionIntegers K ↔
      v.valuation K a ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (a : v.adicCompletion K) ≤ 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- The outside-S mask on a principal finite adele selects precisely S-integers. -/
theorem outsideIntegral_principal_iff_sInteger
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) :
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) v ∈ v.adicCompletionIntegers K) ↔
      a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  change (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    algebraMap K (v.adicCompletion K) a ∈ v.adicCompletionIntegers K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v.valuation K a ≤ 1
  simp only [localIntegral_algebraMap_iff]

/-- The actual S-local tensor evaluated at a global field element. -/
def sIntegerTensorTerm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ) (a : K) : ℂ :=
  φ (mixedEmbedding K a) * ∏ v ∈ S, h v (algebraMap K (v.adicCompletion K) a)

/-- Principal evaluation includes the exact outside-S mask. -/
theorem sIntegerAdelicTestFunction_principal
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ) (a : K) :
    sIntegerAdelicTestFunction K S φ h (algebraMap K (AdeleRing (𝓞 K) K) a) =
      if a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K then
        sIntegerTensorTerm K S φ h a else 0 := by
  unfold sIntegerAdelicTestFunction sIntegerFiniteMask sIntegerTensorTerm
  change φ (InfiniteAdeleRing.ringEquiv_mixedSpace K
    (algebraMap K (InfiniteAdeleRing K) a)) *
      ((∏ v ∈ S, h v (algebraMap K (v.adicCompletion K) a)) *
        if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
          (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) v ∈ v.adicCompletionIntegers K
        then 1 else 0) = _
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  by_cases ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K
  · rw [ite_eq_left ha, ite_eq_left ((outsideIntegral_principal_iff_sInteger K S a).mpr ha)]
    simp
  · have hout := mt (outsideIntegral_principal_iff_sInteger K S a).mp ha
    rw [ite_eq_right ha, ite_eq_right hout]
    simp

/-- Reindex the supported full field sum by the actual S-integer subtype.
This is a literal support identity; it does not assume summability. -/
theorem tsum_sIntegerTensorTerm_eq_tsum_adelic
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ) :
    (∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
      sIntegerTensorTerm K S φ h a.val) =
    ∑' a : K, sIntegerAdelicTestFunction K S φ h
      (algebraMap K (AdeleRing (𝓞 K) K) a) := by
  change (∑' a : {a : K // a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K},
    sIntegerTensorTerm K S φ h a.val) = _
  calc
    _ = ∑' a : K,
        ({a : K | a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K}).indicator
          (sIntegerTensorTerm K S φ h) a :=
      tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro a
      rw [sIntegerAdelicTestFunction_principal]
      rfl

/-- Absolute convergence is inherited from genuine adelic pure-tensor summability. -/
theorem summable_sIntegerTensorTerm
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    Summable fun a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K =>
      sIntegerTensorTerm K S φ h a.val := by
  have hf := summable_comp_algebraMap_of_mem_pureTensorSet
    (sIntegerAdelicTestFunction_mem_pureTensorSet K S φ h hlc hcs)
  have hs := hf.subtype (fun a : K =>
    a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
  apply hs.congr
  intro a
  change sIntegerAdelicTestFunction K S φ h
    (algebraMap K (AdeleRing (𝓞 K) K) a.val) = _
  rw [sIntegerAdelicTestFunction_principal, ite_eq_left a.property]

section Poisson

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- Exact S-integer Poisson summation with the genuine full-adelic transform.
The Haar box factor remains visible, and zero belongs to both full sums. -/
theorem sIntegerAdelicPoisson
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    (∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
      sIntegerTensorTerm K S φ h a.val) =
    ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
      ∑' a : K, fourierIntegral (StandardAddChar.stdAddChar K) μ
        (sIntegerAdelicTestFunction K S φ h) (algebraMap K (AdeleRing (𝓞 K) K) a) := by
  rw [tsum_sIntegerTensorTerm_eq_tsum_adelic]
  exact tsum_eq_inv_measure_mul_tsum_fourierIntegral K μ
    (StandardAddChar.isGlobalAddChar_stdAddChar K)
    (sIntegerAdelicTestFunction_mem_schwartzBruhat K S φ h hlc hcs)

/-- The exact separated dual zero orbit is the integral of the actual test function. -/
theorem sIntegerAdelicPoisson_sub_zeroFrequency
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝓢(mixedEmbedding.mixedSpace K, ℂ))
    (h : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    (∑' a : (S : Set (HeightOneSpectrum (𝓞 K))).integer K,
      sIntegerTensorTerm K S φ h a.val) -
      ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
        ∫ x, sIntegerAdelicTestFunction K S φ h x ∂μ =
    ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
      ∑' a : {a : K // a ≠ 0}, fourierIntegral (StandardAddChar.stdAddChar K) μ
        (sIntegerAdelicTestFunction K S φ h)
        (algebraMap K (AdeleRing (𝓞 K) K) a.val) := by
  rw [tsum_sIntegerTensorTerm_eq_tsum_adelic]
  exact tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
    K μ (StandardAddChar.isGlobalAddChar_stdAddChar K)
    (sIntegerAdelicTestFunction_mem_schwartzBruhat K S φ h hlc hcs)

end Poisson

end HeckeGeneral.Bridge
