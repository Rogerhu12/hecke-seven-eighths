import HeckeGeneral.Bridge.SIntegerFourierFactorization
import HeckeGeneral.Arithmetic.SUnitCompactDenominators
import FLTReuse.M88e60ad1fc5ea3de

/-!
# Compact finite-local Fourier profiles

The normalized product of the actual local Fourier transforms is locally
constant and compactly supported on the additive S-product. This is derived
from the finite-adelic Fourier theorem and the actual zero extension. The
support is bounded by the projection of a compact adelic support; no assertion
that an arbitrary continuous pullback preserves compact support is used.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier
  NumberField.StandardAddChar HeckeGeneral.Characters HeckeGeneral.Arithmetic
  MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Restrict a finite adele to its actual S-coordinates. -/
def finiteAdeleLocalProjection (w : FiniteAdeleRing (𝓞 K) K) :
    (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K :=
  fun v => w v.val

theorem continuous_finiteAdeleLocalProjection :
    Continuous (finiteAdeleLocalProjection K S) :=
  continuous_pi fun v => RestrictedProduct.continuous_eval v.val

@[simp] theorem finiteAdeleLocalProjection_zeroExtension
    (z : (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) :
    finiteAdeleLocalProjection K S
      (finiteLocalZeroExtension K (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet z) = z := by
  funext v
  exact finiteLocalZeroExtension_apply_mem K _ S.finite_toSet z v.val v.property

/-- The zero extension has a continuous left inverse. Its pullback support
therefore lies in a compact projection of the original support. -/
theorem hasCompactSupport_comp_finiteLocalZeroExtension
    {f : FiniteAdeleRing (𝓞 K) K → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => f
      (finiteLocalZeroExtension K (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet z)) := by
  have hC := hf.isCompact.image (continuous_finiteAdeleLocalProjection K S)
  apply hC.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hC.isClosed
  intro z hz
  refine ⟨finiteLocalZeroExtension K _ S.finite_toSet z, subset_closure hz, ?_⟩
  exact finiteAdeleLocalProjection_zeroExtension K S z

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The normalized local transforms evaluated on the additive S-product. -/
def sIntegerFiniteFourierTestFunction
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (z : (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) : ℂ :=
  ∏ v : (S : Set (HeightOneSpectrum (𝓞 K))),
    (((μv v.val).real (v.val.adicCompletionIntegers K : Set (v.val.adicCompletion K)) : ℂ))⁻¹ *
      fourierIntegral (psiLocal K v.val) (μv v.val) (h v.val) (z v)

theorem sIntegerLocalFourierProduct_eq_finiteFourierTestFunction
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (w : FiniteAdeleRing (𝓞 K) K) :
    sIntegerLocalFourierProduct K μv S h w =
      sIntegerFiniteFourierTestFunction K S μv h (finiteAdeleLocalProjection K S w) := by
  unfold sIntegerLocalFourierProduct sIntegerFiniteFourierTestFunction finiteAdeleLocalProjection
  exact (Finset.prod_finset_coe (fun v : HeightOneSpectrum (𝓞 K) =>
    (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
      fourierIntegral (psiLocal K v) (μv v) (h v) (w v)) S).symm

/-- At zero extension the outside-S annihilator indicator equals one. -/
theorem outsideSStandardAnnihilator_zeroExtension
    (z : (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) :
    outsideSStandardAnnihilator K S
      (finiteLocalZeroExtension K (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet z) := by
  intro v hv a _ha
  rw [finiteLocalZeroExtension_apply_notMem K _ S.finite_toSet z v hv, mul_zero]
  exact AddChar.map_zero_eq_one _

theorem sIntegerFiniteFourierTestFunction_eq_adelic_pullback
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (z : (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) :
    sIntegerFiniteFourierTestFunction K S μv h z =
      ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
        fourierIntegral (standardFiniteAddCharacter K) ν (sIntegerFiniteMask K S h)
          (finiteLocalZeroExtension K (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet z) := by
  rw [sIntegerFiniteMask_fourier_factorization K ν μv S h hlc hcs,
    if_pos (outsideSStandardAnnihilator_zeroExtension K S z), mul_one,
    sIntegerLocalFourierProduct_eq_finiteFourierTestFunction K S μv,
    finiteAdeleLocalProjection_zeroExtension]

include ν in
/-- Actual Fourier closure, with compact support proved from the adelic theorem. -/
theorem sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (sIntegerFiniteFourierTestFunction K S μv h) ∧
      HasCompactSupport (sIntegerFiniteFourierTestFunction K S μv h) := by
  have hmask := sIntegerFiniteMask_locallyConstant_compactSupport K S h hlc hcs
  have hft := isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
    K ν (isGlobalAddChar_stdAddChar K)
    (stdAddChar_apply_mk_zero_eq_fourierChar_trace K) hmask.1 hmask.2
  change IsLocallyConstant
      (fourierIntegral (standardFiniteAddCharacter K) ν (sIntegerFiniteMask K S h)) ∧
    HasCompactSupport
      (fourierIntegral (standardFiniteAddCharacter K) ν (sIntegerFiniteMask K S h)) at hft
  have hcomp := hft.1.comp_continuous
    (continuous_finiteLocalZeroExtension K (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet)
  have hsupport := hasCompactSupport_comp_finiteLocalZeroExtension K S hft.2
  have heq : sIntegerFiniteFourierTestFunction K S μv h =
      fun z => ((ν.real (AdelicBox.integralFiniteAdeles (𝓞 K) K) : ℂ))⁻¹ *
        fourierIntegral (standardFiniteAddCharacter K) ν (sIntegerFiniteMask K S h)
          (finiteLocalZeroExtension K (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet z) := by
    funext z
    exact sIntegerFiniteFourierTestFunction_eq_adelic_pullback K S ν μv h hlc hcs z
  rw [heq]
  exact ⟨(IsLocallyConstant.const _).mul hcomp, hsupport.mul_left⟩

end HeckeGeneral.Bridge
