import HeckeGeneral.Bridge.ScaledAdelicPoisson
import HeckeGeneral.Bridge.SIntegerSelfDualPoisson

/-!
# S-integer Poisson at every actual local multiplicative base point

The assembled idele has coordinate one outside S, so dilation preserves the
actual S-integer support. After S contains the different primes, the Fourier
support is the same actual ring. Both full sums below still include zero.
The inverse local point and the true product-norm factor are retained.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier
  NumberField.StandardAddChar HeckeGeneral.Characters HeckeGeneral.Arithmetic
  MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K

/-- The actual assembled dilation of a principal adele, including at zero. -/
def sLocalScaledPrincipal (p : G) (a : K) : AdeleRing (𝓞 K) K :=
  (sLocalIdeleAssembly K (S : Set (HeightOneSpectrum (𝓞 K))) p).val *
    algebraMap K (AdeleRing (𝓞 K) K) a

@[simp] theorem sLocalScaledPrincipal_zero (p : G) :
    sLocalScaledPrincipal K S p 0 = 0 := by
  simp [sLocalScaledPrincipal]

@[simp] theorem sLocalScaledPrincipal_arch (p : G) (a : K) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (sLocalScaledPrincipal K S p a).1 =
      p.1.val * mixedEmbedding K a := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace K
    ((sLocalIdeleAssembly K _ p).val.1 * algebraMap K (InfiniteAdeleRing K) a) = _
  rw [map_mul, sLocalIdeleAssembly_arch,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

@[simp] theorem sLocalScaledPrincipal_finite_mem (p : G) (a : K)
    (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    (sLocalScaledPrincipal K S p a).2 v.val =
      (p.2 v).val * algebraMap K (v.val.adicCompletion K) a := by
  change (sLocalIdeleAssembly K _ p).val.2 v.val *
    algebraMap K (v.val.adicCompletion K) a = _
  rw [sLocalIdeleAssembly_finite_mem]

@[simp] theorem sLocalScaledPrincipal_finite_not_mem (p : G) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    (sLocalScaledPrincipal K S p a).2 v = algebraMap K (v.adicCompletion K) a := by
  change (sLocalIdeleAssembly K _ p).val.2 v *
    algebraMap K (v.adicCompletion K) a = _
  rw [sLocalIdeleAssembly_finite_not_mem K _ p v hv, one_mul]

/-- Multiplication by the assembled idele changes no outside-S condition. -/
theorem outsideIntegral_sLocalScaledPrincipal_iff (p : G) (a : K) :
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (sLocalScaledPrincipal K S p a).2 v ∈ v.adicCompletionIntegers K) ↔ a ∈ OS := by
  rw [← outsideIntegral_principal_iff_sInteger K S a]
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [sLocalScaledPrincipal_finite_not_mem K S p a v hv]
  rfl

theorem outsideSStandardAnnihilator_sLocalScaledPrincipal_iff
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (p : G) (a : K) :
    outsideSStandardAnnihilator K S (sLocalScaledPrincipal K S p a).2 ↔ a ∈ OS := by
  rw [← outsideSStandardAnnihilator_principal_iff_sInteger K S hS a]
  unfold outsideSStandardAnnihilator
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [sLocalScaledPrincipal_finite_not_mem K S p a v hv]
  rfl

/-- The original test function at an actual scaled principal point. -/
def sIntegerScaledTensorTerm (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (p : G) (a : K) : ℂ :=
  sIntegerAdelicTestFunction K S φ h (sLocalScaledPrincipal K S p a)

theorem sIntegerScaledTensorTerm_eq_zero_of_not_mem
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (p : G) (a : K) (ha : a ∉ OS) : sIntegerScaledTensorTerm K S φ h p a = 0 := by
  unfold sIntegerScaledTensorTerm sIntegerAdelicTestFunction sIntegerFiniteMask
  rw [if_neg (mt (outsideIntegral_sLocalScaledPrincipal_iff K S p a).mp ha),
    mul_zero, mul_zero]

/-- The full field sum is supported on the genuine S-integer subring. -/
theorem tsum_sIntegerScaledTensorTerm_eq_tsum_field
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) (p : G) :
    (∑' a : OS, sIntegerScaledTensorTerm K S φ h p a.val) =
      ∑' a : K, sIntegerScaledTensorTerm K S φ h p a := by
  change (∑' a : {a : K // a ∈ OS}, sIntegerScaledTensorTerm K S φ h p a.val) = _
  calc
    _ = ∑' a : K, ({a : K | a ∈ OS}).indicator
        (sIntegerScaledTensorTerm K S φ h p) a := tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro a
      by_cases ha : a ∈ OS
      · exact Set.indicator_of_mem ha _
      · rw [Set.indicator_of_notMem (show a ∉ {a : K | a ∈ OS} from ha),
          sIntegerScaledTensorTerm_eq_zero_of_not_mem K S φ h p a ha]

theorem summable_sIntegerScaledTensorTerm
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (p : G) :
    Summable (fun a : OS => sIntegerScaledTensorTerm K S φ h p a.val) := by
  have hg := comp_mul_mem_schwartzBruhat K (sLocalIdeleAssembly K _ p)
    (sIntegerAdelicTestFunction_mem_schwartzBruhat K S φ h hlc hcs)
  have hs := summable_translate_of_mem_schwartzBruhat K hg 0
  have hf : Summable (fun a : K => sIntegerScaledTensorTerm K S φ h p a) := by
    simpa only [zero_add, sIntegerScaledTensorTerm, sLocalScaledPrincipal] using hs
  exact hf.subtype (fun a : K => a ∈ OS)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The two actual Fourier factors at the scaled frequency. -/
def sIntegerScaledDualTensorTerm (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (p : G) (a : K) : ℂ :=
  fourierIntegral (standardMixedAddCharacter K) volume φ
      (InfiniteAdeleRing.ringEquiv_mixedSpace K (sLocalScaledPrincipal K S p a).1) *
    sIntegerLocalFourierProduct K μv S h (sLocalScaledPrincipal K S p a).2

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν in
theorem sIntegerScaledFourier_eq_supported_dual
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (p : G) (a : K) :
    ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ *
      fourierIntegral (stdAddChar K) μ (sIntegerAdelicTestFunction K S φ h)
        (sLocalScaledPrincipal K S p a) =
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      (if a ∈ OS then sIntegerScaledDualTensorTerm K S μv φ h p a else 0) := by
  rw [sIntegerAdelicTestFunction_fourier_factorization K ν μv μ S φ h hlc hcs,
    outsideSStandardAnnihilator_sLocalScaledPrincipal_iff K S hS p a]
  by_cases ha : a ∈ OS <;> simp [ha, sIntegerScaledDualTensorTerm]

include μ ν in
/-- Full S-integer Poisson under arbitrary genuine local dilation. -/
theorem sIntegerScaledPoisson
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (p : G) :
    (∑' a : OS, sIntegerScaledTensorTerm K S φ h p a.val) =
      (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        ∑' a : OS, sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ a.val := by
  let C : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
  let b : ℂ := ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹
  let n : ℂ := (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹
  have hp := scaledAdelicPoisson K μ (sIntegerAdelicTestFunction K S φ h)
    (sIntegerAdelicTestFunction_mem_schwartzBruhat K S φ h hlc hcs)
    (sLocalIdeleAssembly K (S : Set (HeightOneSpectrum (𝓞 K))) p)
  rw [idelicNorm_sLocalIdeleAssembly, ← map_inv] at hp
  have hreindex : (∑' a : K, if a ∈ OS then
        sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ a else 0) =
      ∑' a : OS, sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ a.val := by
    change _ = ∑' a : {a : K // a ∈ OS}, _
    exact (tsum_subtype _ _).symm
  rw [tsum_sIntegerScaledTensorTerm_eq_tsum_field]
  change (∑' a : K, sIntegerScaledTensorTerm K S φ h p a) =
    n * C * ∑' a : OS, sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ a.val
  calc
    _ = b * n * ∑' a : K,
        fourierIntegral (stdAddChar K) μ (sIntegerAdelicTestFunction K S φ h)
          (sLocalScaledPrincipal K S p⁻¹ a) := hp
    _ = n * ∑' a : K, b *
        fourierIntegral (stdAddChar K) μ (sIntegerAdelicTestFunction K S φ h)
          (sLocalScaledPrincipal K S p⁻¹ a) := by rw [tsum_mul_left]; ring
    _ = n * ∑' a : K, C * (if a ∈ OS then
        sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ a else 0) := by
      congr 1
      apply tsum_congr
      intro a
      exact sIntegerScaledFourier_eq_supported_dual K S ν μv μ hS φ h hlc hcs p⁻¹ a
    _ = _ := by rw [tsum_mul_left, hreindex, mul_assoc]

include μ ν in
/-- Actual Fourier summability also survives every local dilation. -/
theorem summable_sIntegerScaledDualTensorTerm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (p : G) :
    Summable (fun a : OS => sIntegerScaledDualTensorTerm K S μv φ h p a.val) := by
  have hF := fourierIntegral_mem_schwartzBruhat K μ (isGlobalAddChar_stdAddChar K)
    (sIntegerAdelicTestFunction_mem_schwartzBruhat K S φ h hlc hcs)
  have hg := comp_mul_mem_schwartzBruhat K (sLocalIdeleAssembly K _ p) hF
  have hs : Summable (fun a : K =>
      fourierIntegral (stdAddChar K) μ (sIntegerAdelicTestFunction K S φ h)
        (sLocalScaledPrincipal K S p a)) := by
    simpa only [zero_add, sLocalScaledPrincipal] using
      summable_translate_of_mem_schwartzBruhat K hg 0
  have hn := (hs.subtype (fun a : K => a ∈ OS)).mul_left
    (((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹)
  have hp : Summable (fun a : OS =>
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
        Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        sIntegerScaledDualTensorTerm K S μv φ h p a.val) := by
    apply hn.congr
    intro a
    simpa only [Function.comp_apply, a.property, if_true] using
      sIntegerScaledFourier_eq_supported_dual K S ν μv μ hS φ h hlc hcs p a.val
  exact (summable_mul_left_iff (sIntegerDiscriminantFactor_ne_zero K)).mp hp

include μ ν in
/-- Both zero contributions remain explicit when removing zero from the sums. -/
theorem sIntegerScaledPoisson_nonzero
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (p : G) :
    let c : ℂ :=
      (sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) p : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    (∑' a : {a : OS // a ≠ 0}, sIntegerScaledTensorTerm K S φ h p a.val.val) =
      c * (∑' a : {a : OS // a ≠ 0},
        sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ a.val.val) +
      c * sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ 0 -
        sIntegerScaledTensorTerm K S φ h p 0 := by
  dsimp only
  have he := sIntegerScaledPoisson K S ν μv μ hS φ h hlc hcs p
  rw [tsum_eq_zero_add_tsum_ne_zero _ (summable_sIntegerScaledTensorTerm K S φ h hlc hcs p),
    tsum_eq_zero_add_tsum_ne_zero _
      (summable_sIntegerScaledDualTensorTerm K S ν μv μ hS φ h hlc hcs p⁻¹)] at he
  change sIntegerScaledTensorTerm K S φ h p 0 + _ =
    _ * (sIntegerScaledDualTensorTerm K S μv φ h p⁻¹ 0 + _) at he
  linear_combination he

end HeckeGeneral.Bridge
