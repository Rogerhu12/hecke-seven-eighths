import HeckeGeneral.Bridge.SIntegerPeriodicFiniteTest
import HeckeGeneral.Bridge.SIntegerScaledPoisson

/-!
# Actual adelic Poisson for an arbitrary periodic S-integer coefficient

The finite residue test is paired with the original archimedean Schwartz
function. Its principal evaluations give the literal periodic coefficient
on the original S-integers at every original S-local multiplicative point.
Absolute summability and Poisson follow from the genuine adelic theorem.
The right side here is the actual Fourier integral; identification with
the explicit divisor transform and separation of zero orbits are subsequent
steps, not hypotheses or definitions of this test function.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  NumberField.AdelicFourier NumberField.StandardAddChar MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)


local notation "P" => sIntegerModulusPlaces K (S : Set (HeightOneSpectrum (𝓞 K))) c hc

def sIntegerPeriodicAdelicTest
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (z : AdeleRing (𝓞 K) K) : ℂ :=
  φ (InfiniteAdeleRing.ringEquiv_mixedSpace K z.1) *
    sIntegerPeriodicFiniteTest K S c hc h f d z.2

theorem sIntegerPeriodicAdelicTest_mem_pureTensorSet
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) :
    sIntegerPeriodicAdelicTest K S c hc φ h f d ∈ pureTensorSet K := by
  have hf := sIntegerPeriodicFiniteTest_locallyConstant_compactSupport
    K S c hc h hlc hcs f d
  exact tensor_mem_pureTensorSet φ _ hf.1 hf.2

theorem sIntegerPeriodicAdelicTest_mem_schwartzBruhat
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) :
    sIntegerPeriodicAdelicTest K S c hc φ h f d ∈ schwartzBruhat K :=
  mem_schwartzBruhat_of_mem_pureTensorSet
    (sIntegerPeriodicAdelicTest_mem_pureTensorSet K S c hc φ h hlc hcs f d)

/-- The residue coefficient is unchanged by the original S-local dilation. -/
theorem sIntegerPeriodicAdelicTest_scaled_sInteger
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d a : OS) (p : G) :
    sIntegerPeriodicAdelicTest K S c hc φ h f d (sLocalScaledPrincipal K S p a.val) =
      f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a)) *
        sIntegerScaledTensorTerm K S φ h p a.val := by
  have hout := (outsideIntegral_sLocalScaledPrincipal_iff K S p a.val).mpr a.property
  have houtU : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ P →
      (sLocalScaledPrincipal K S p a.val).2 v ∈ v.adicCompletionIntegers K :=
    fun v hv => hout v (fun hvS => hv (Finset.mem_union_left P hvS))
  have hcoord (v : P) : (sLocalScaledPrincipal K S p a.val).2 v.val =
      algebraMap K (v.val.adicCompletion K) a.val :=
    sLocalScaledPrincipal_finite_not_mem K S p a.val v.val
      (sIntegerModulusPlaces_not_mem K _ c hc v)
  unfold sIntegerPeriodicAdelicTest
  rw [sIntegerPeriodicFiniteTest_apply K S c hc h f d a _ houtU hcoord]
  unfold sIntegerScaledTensorTerm sIntegerAdelicTestFunction sIntegerFiniteMask
  rw [if_pos hout, mul_one]
  ring

theorem sIntegerPeriodicAdelicTest_scaled_zero_of_not_mem
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) (a : K) (ha : a ∉ OS) :
    sIntegerPeriodicAdelicTest K S c hc φ h f d (sLocalScaledPrincipal K S p a) = 0 := by
  unfold sIntegerPeriodicAdelicTest
  rw [sIntegerPeriodicFiniteTest_zero_of_not_integral K S c hc h f d _
    (mt (outsideIntegral_sLocalScaledPrincipal_iff K S p a).mp ha), mul_zero]

include hc in
theorem summable_sIntegerPeriodicScaledTensor
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) :
    Summable (fun a : OS => f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a)) *
      sIntegerScaledTensorTerm K S φ h p a.val) := by
  have hg := comp_mul_mem_schwartzBruhat K (sLocalIdeleAssembly K _ p)
    (sIntegerPeriodicAdelicTest_mem_schwartzBruhat K S c hc φ h hlc hcs f d)
  have hs := summable_translate_of_mem_schwartzBruhat K hg 0
  have hf : Summable (fun a : K => sIntegerPeriodicAdelicTest K S c hc φ h f d
      (sLocalScaledPrincipal K S p a)) := by
    simpa only [zero_add, sLocalScaledPrincipal] using hs
  exact (hf.subtype (fun a : K => a ∈ OS)).congr
    (fun a => sIntegerPeriodicAdelicTest_scaled_sInteger K S c hc φ h f d a p)

theorem tsum_sIntegerPeriodicScaledTensor_eq_tsum_field
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) :
    (∑' a : OS, f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a)) *
      sIntegerScaledTensorTerm K S φ h p a.val) =
      ∑' a : K, sIntegerPeriodicAdelicTest K S c hc φ h f d
        (sLocalScaledPrincipal K S p a) := by
  calc
    _ = ∑' a : OS, sIntegerPeriodicAdelicTest K S c hc φ h f d
        (sLocalScaledPrincipal K S p a.val) := by
      apply tsum_congr
      intro a
      exact (sIntegerPeriodicAdelicTest_scaled_sInteger K S c hc φ h f d a p).symm
    _ = ∑' a : K, ({a : K | a ∈ OS}).indicator
        (fun b => sIntegerPeriodicAdelicTest K S c hc φ h f d
          (sLocalScaledPrincipal K S p b)) a :=
      tsum_subtype {a : K | a ∈ OS}
        (fun b => sIntegerPeriodicAdelicTest K S c hc φ h f d
          (sLocalScaledPrincipal K S p b))
    _ = _ := by
      apply tsum_congr
      intro a
      by_cases ha : a ∈ OS
      · exact Set.indicator_of_mem ha _
      · rw [Set.indicator_of_notMem (show a ∉ {a : K | a ∈ OS} from ha),
          sIntegerPeriodicAdelicTest_scaled_zero_of_not_mem K S c hc φ h f d p a ha]

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- Periodic Poisson with the actual Fourier integral and both zero terms.
The finite-frequency formula and zero-orbit subtraction have not been substituted. -/
theorem sIntegerPeriodicScaledAdelicPoisson
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (p : G) :
    (∑' a : OS, f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a)) *
      sIntegerScaledTensorTerm K S φ h p a.val) =
      ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
        (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹ *
          ∑' a : K, fourierIntegral (stdAddChar K) μ
            (sIntegerPeriodicAdelicTest K S c hc φ h f d)
            (sLocalScaledPrincipal K S p⁻¹ a) := by
  rw [tsum_sIntegerPeriodicScaledTensor_eq_tsum_field]
  simpa only [sLocalScaledPrincipal, map_inv, idelicNorm_sLocalIdeleAssembly] using
    scaledAdelicPoisson K μ (sIntegerPeriodicAdelicTest K S c hc φ h f d)
      (sIntegerPeriodicAdelicTest_mem_schwartzBruhat K S c hc φ h hlc hcs f d)
      (sLocalIdeleAssembly K (S : Set (HeightOneSpectrum (𝓞 K))) p)

end HeckeGeneral.Bridge

