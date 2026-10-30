import HeckeGeneral.Bridge.SIntegerScaledPoisson
import HeckeGeneral.Bridge.TraceSchwartzFourier
import HeckeGeneral.Bridge.SLocalFiniteFourier

/-!
# The scaled Poisson terms are the actual orbital Schwartz tensors

At every nonzero S-integer, both sides of the scaled adelic formula are
identified with the same local model used for orbital integration. The dual
infinite factor is the actual trace Fourier Schwartz map, and the dual finite
factor has proved locally constant compact support. Zero is handled by its
actual test-function value rather than by extending a radial profile to zero.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier
  HeckeGeneral.Arithmetic HeckeGeneral.Analysis MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K

/-- A scaled nonzero principal term is exactly the original orbital tensor. -/
theorem sIntegerScaledTensorTerm_eq_sLocalTensor
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (p : G) (a : NonzeroRingElements OS) :
    sIntegerScaledTensorTerm K S (traceSchwartzToMixed K φ) h p a.val.val =
      sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ
        (sIntegerFiniteTestFunction K S h)
        (p * sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K))) a) := by
  unfold sIntegerScaledTensorTerm sIntegerAdelicTestFunction sIntegerFiniteMask
  rw [if_pos ((outsideIntegral_sLocalScaledPrincipal_iff K S p a.val.val).mpr a.val.property),
    mul_one, sLocalScaledPrincipal_arch]
  rw [← Finset.prod_finset_coe]
  simp only [sLocalScaledPrincipal_finite_mem]
  rfl

theorem sIntegerScaledTensorTerm_zero
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) (p : G) :
    sIntegerScaledTensorTerm K S (traceSchwartzToMixed K φ) h p 0 =
      sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0 := by
  unfold sIntegerScaledTensorTerm
  rw [sLocalScaledPrincipal_zero]
  have hz := sIntegerAdelicTestFunction_principal K S (traceSchwartzToMixed K φ) h 0
  simpa only [map_zero, zero_mem, if_true] using hz

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Restriction of the actual scaled frequency gives the local diagonal product. -/
theorem finiteAdeleLocalProjection_sLocalScaledPrincipal
    (p : G) (a : NonzeroRingElements OS) :
    finiteAdeleLocalProjection K S (sLocalScaledPrincipal K S p a.val.val).2 =
      fun v : (S : Set (HeightOneSpectrum (𝓞 K))) =>
        ((p * sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K))) a).2 v).val := by
  funext v
  exact sLocalScaledPrincipal_finite_mem K S p a.val.val v

/-- The Fourier side is an actual Schwartz tensor in precisely the same model. -/
theorem sIntegerScaledDualTensorTerm_eq_sLocalTensor
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (p : G) (a : NonzeroRingElements OS) :
    sIntegerScaledDualTensorTerm K S μv (traceSchwartzToMixed K φ) h p a.val.val =
      sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
        (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h)
        (p * sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K))) a) := by
  unfold sIntegerScaledDualTensorTerm
  rw [← mixedTraceSchwartzFourier_apply,
    sIntegerLocalFourierProduct_eq_finiteFourierTestFunction,
    finiteAdeleLocalProjection_sLocalScaledPrincipal, sLocalScaledPrincipal_arch]
  rfl

theorem sIntegerScaledDualTensorTerm_zero
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) (p : G) :
    sIntegerScaledDualTensorTerm K S μv (traceSchwartzToMixed K φ) h p 0 =
      sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0 := by
  unfold sIntegerScaledDualTensorTerm sIntegerDualTensorTerm
  rw [sLocalScaledPrincipal_zero, map_zero]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

include ν Γ in
/-- Fourier-side orbital integrability is proved for the actual transformed data. -/
theorem integrable_sIntegerFourierTensor_orbit
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (p : G) :
    Integrable (fun x : sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))) =>
      sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
        (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h) (p * x.val))
      (sUnitHaarMeasure K (S : Set (HeightOneSpectrum (𝓞 K)))) := by
  have hfinite := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  exact integrable_sLocalTensorTestFunction_orbit K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h)
    hfinite.1.continuous hfinite.2 p

end HeckeGeneral.Bridge
