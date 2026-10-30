import HeckeGeneral.Bridge.SIntegerAdelicPoisson
import HeckeGeneral.Analysis.SIntegerOrbitUnfolding
import Mathlib.Topology.Compactness.Compact

/-!
# The same test function in adelic Poisson and norm-one orbit integration

The trace-Euclidean Schwartz function is transported through the actual
trace-to-mixed linear equivalence. The finite local function is the literal
product of the local factors used in the adelic Poisson theorem. Its
continuity and additive compact support are proved from those factors.
Principal evaluation then identifies the two test functions exactly.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Change only the archimedean coordinate model, through its actual equivalence. -/
def traceSchwartzToMixed (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    SchwartzMap (mixedEmbedding.mixedSpace K) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceToMixed K).symm φ

@[simp] theorem traceSchwartzToMixed_apply
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (x : mixedEmbedding.mixedSpace K) :
    traceSchwartzToMixed K φ x = φ ((traceToMixed K).symm x) := rfl

/-- The actual finite tensor on the additive product, including zero coordinates. -/
def sIntegerFiniteTestFunction
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (z : (v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) : ℂ :=
  ∏ v : (S : Set (HeightOneSpectrum (𝓞 K))), h v.val (z v)

theorem continuous_sIntegerFiniteTestFunction
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) :
    Continuous (sIntegerFiniteTestFunction K S h) := by
  apply continuous_finsetProd Finset.univ
  intro v _hv
  exact (hlc v.val v.property).continuous.comp (continuous_apply v)

theorem hasCompactSupport_sIntegerFiniteTestFunction
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    HasCompactSupport (sIntegerFiniteTestFunction K S h) := by
  let C : Set ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) :=
    Set.univ.pi (fun v => tsupport (h v.val))
  have hC : IsCompact C := isCompact_univ_pi (fun v => (hcs v.val v.property).isCompact)
  apply hC.of_isClosed_subset (isClosed_tsupport (sIntegerFiniteTestFunction K S h))
  apply closure_minimal _ hC.isClosed
  intro z hz v _hv
  apply subset_closure
  intro hzero
  exact hz (Finset.prod_eq_zero (Finset.mem_univ v) hzero)

/-- Nonzero principal evaluation is literally the same tensor in both models. -/
theorem sLocalTensorTestFunction_nonzeroIntegerDiagonal
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (a : NonzeroRingElements ((S : Set (HeightOneSpectrum (𝓞 K))).integer K)) :
    sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ
      (sIntegerFiniteTestFunction K S h)
      (sLocalNonzeroIntegerDiagonal K (S : Set (HeightOneSpectrum (𝓞 K))) a) =
      sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h (a.val : K) := by
  change φ ((traceToMixed K).symm (mixedEmbedding K (a.val : K))) *
      (∏ v : (S : Set (HeightOneSpectrum (𝓞 K))),
        h v.val (algebraMap K (v.val.adicCompletion K) (a.val : K))) =
    φ ((traceToMixed K).symm (mixedEmbedding K (a.val : K))) *
      ∏ v ∈ S, h v (algebraMap K (v.adicCompletion K) (a.val : K))
  exact congrArg (fun z : ℂ =>
    φ ((traceToMixed K).symm (mixedEmbedding K (a.val : K))) * z)
    (Finset.prod_finset_coe
      (fun v : HeightOneSpectrum (𝓞 K) =>
        h v (algebraMap K (v.adicCompletion K) (a.val : K))) S)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

include Γ in
/-- The very same local factors as Poisson give an integrable orbit at every
actual nonzero local base point, with no added analytic hypothesis. -/
theorem integrable_sIntegerLocalTensor_orbit
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (p : sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))) :
    Integrable (fun x : sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))) =>
      sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ
        (sIntegerFiniteTestFunction K S h) (p * x.val))
      (sUnitHaarMeasure K (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  integrable_sLocalTensorTestFunction_orbit K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    φ (sIntegerFiniteTestFunction K S h)
    (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) p

end HeckeGeneral.Bridge
