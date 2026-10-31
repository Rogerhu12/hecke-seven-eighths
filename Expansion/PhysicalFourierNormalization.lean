import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.SIntegerPeriodicOrbitalPoisson

/-!
# The literal physical Fourier tensor in genuine orbital Poisson

The Fourier tensor of `ProbeData.additive` is precisely the normalized
local tensor used by S-integer Poisson.  There is no implicit discriminant
factor in this identification.  Consequently the explicit positive
`physicalPoissonScalar` occurs in the orbital identity below.

This is an identity for the actual test and every actual finite periodic
coefficient.  It keeps both zero terms.  The subsequent construction of
the Gauss-symbol coefficient and the completed-theta/Mellin interchanges
are separate obligations; they are not hypotheses disguising this identity.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalFourierNormalization

open NumberField IsDedekindDomain MeasureTheory
open NumberField.AdelicFourier
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "G" => sLocalMultiplicativeGroup K Sset

/-- Extend the actual finite test to the ambient set of places.  Only
coordinates in `S` enter any tensor or finite Fourier transform. -/
def finiteExtension (W : AdditiveProbeTest K Sset)
    (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K → ℂ :=
  if hv : v ∈ S then W.finiteTest ⟨v, hv⟩ else 0

@[simp] theorem finiteExtension_subtype (W : AdditiveProbeTest K Sset) (v : Sset) :
    finiteExtension K S W v.val = W.finiteTest v := by
  unfold finiteExtension
  rw [dif_pos v.property]

theorem finiteExtension_locallyConstant (W : AdditiveProbeTest K Sset)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    IsLocallyConstant (finiteExtension K S W v) := by
  simpa only [finiteExtension, dif_pos hv] using W.finite_locallyConstant ⟨v, hv⟩

theorem finiteExtension_compactSupport (W : AdditiveProbeTest K Sset)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    HasCompactSupport (finiteExtension K S W v) := by
  simpa only [finiteExtension, dif_pos hv] using W.finite_compactSupport ⟨v, hv⟩

/-- The original physical tensor is the original Poisson tensor, pointwise. -/
theorem additiveTest_eq_tensor (W : AdditiveProbeTest K Sset) :
    additiveTest K Sset W =
      sLocalTensorTestFunction K Sset W.infiniteTest
        (sIntegerFiniteTestFunction K S (finiteExtension K S W)) := by
  funext x
  simp only [additiveTest, sLocalTensorTestFunction, sIntegerFiniteTestFunction,
    finiteExtension_subtype]

/-- The actual value of the additive tensor at the additive origin. -/
def additiveValueAtZero (W : AdditiveProbeTest K Sset) : ℂ :=
  W.infiniteTest 0 * ∏ v : Sset, W.finiteTest v 0

theorem tensor_zero (W : AdditiveProbeTest K Sset) :
    sIntegerTensorTerm K S (traceSchwartzToMixed K W.infiniteTest)
        (finiteExtension K S W) 0 = additiveValueAtZero K S W := by
  unfold sIntegerTensorTerm additiveValueAtZero
  simp only [map_zero, traceSchwartzToMixed_apply]
  rw [← Finset.prod_finset_coe]
  simp only [finiteExtension_subtype]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Literal Fourier identity.  In particular its right side does not
absorb `physicalPoissonScalar`; that factor remains outside Poisson. -/
theorem additiveFourier_eq_tensor (W : AdditiveProbeTest K Sset) :
    additiveFourier K Sset (fun v => μv v.val) W =
      sLocalTensorTestFunction K Sset (traceSchwartzFourier K W.infiniteTest)
        (sIntegerFiniteFourierTestFunction K S μv (finiteExtension K S W)) := by
  funext x
  change fourierIntegral (standardMixedAddCharacter K) volume
      (traceSchwartzToMixed K W.infiniteTest) (x.1 : mixedEmbedding.mixedSpace K) * _ = _
  rw [← mixedTraceSchwartzFourier_apply]
  simp only [mixedTraceSchwartzFourier, traceSchwartzToMixed_apply,
    sLocalTensorTestFunction, sIntegerFiniteFourierTestFunction, finiteExtension_subtype]

/-- The zero Fourier term also has the literal physical normalization. -/
theorem dualTensor_zero (W : AdditiveProbeTest K Sset) :
    sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K W.infiniteTest)
        (finiteExtension K S W) 0 =
      additiveFourierAtZero K Sset (fun v => μv v.val) W := by
  unfold sIntegerDualTensorTerm
  simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
  change fourierIntegral (standardMixedAddCharacter K) volume
      (fun y => W.infiniteTest ((traceToMixed K).symm y)) 0 *
      (∏ v ∈ S,
        (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
          fourierIntegral (StandardAddChar.psiLocal K v) (μv v)
            (finiteExtension K S W v) 0) = _
  rw [← Finset.prod_finset_coe]
  simp only [finiteExtension_subtype, additiveFourierAtZero]

variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
  [BorelSpace (sLocalNormOneGroup K Sset)]
  (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

local notation "Q" => SIntegerOrbits K Sset Γ

/-- Actual weighted orbital sum of a function on the local multiplicative
group, with every original subgroup sector retained. -/
def weightedPhysicalOrbitalSeries (F : G → ℂ)
    (r : {r : ℝ // 0 < r}) (w : Q → ℂ) : ℂ :=
  ∑' q : Q, w q * sUnitOrbitalProfile K Sset F
    ⟨r.val * (sIntegerOrbitNorm K Sset Γ q).val,
      mul_pos r.property (sIntegerOrbitNorm K Sset Γ q).property⟩

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include μ ν in
/-- Genuine orbital Poisson for the actual `ProbeData` test, with its
actual arithmetic different support and both actual zero frequencies.
The only coefficient premise is literal invariance under the given
subgroup; no Poisson equality or analytic interchange is an input. -/
theorem probePeriodicOrbitalPoisson (P : ProbeData K Sset)
    (c : OS) (hc : c ≠ 0) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) (d : OS) (r : {r : ℝ // 0 < r}) :
    let g : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ :=
      fun z => f (Ideal.Quotient.mk _ d * z)
    let hg := sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv d
    let C : ℂ := (r.val : ℂ)⁻¹ * (physicalPoissonScalar K : ℂ) *
      ((sIntegerElementNorm K Sset ⟨c, hc⟩).val : ℂ)⁻¹
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K Sset ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K Sset ⟨c, hc⟩).property)⟩
    weightedPhysicalOrbitalSeries K S Γ (additiveTest K Sset P.additive) r
        (sIntegerPeriodicOrbitWeight K Sset Γ c g hg) =
      C * weightedPhysicalOrbitalSeries K S Γ
        (additiveFourier K Sset (fun v => μv v.val) P.additive) rDual
        (sIntegerPeriodicFourierOrbitWeight K Sset P.arithmetic.different_outside
          Γ c hc f hinv d) +
      ((sUnitHaarCovolume K Sset Γ).toReal : ℂ) *
        (C * (sIntegerPeriodicDivisorFourier K Sset P.arithmetic.different_outside
            c hc f d 0 * additiveFourierAtZero K Sset (fun v => μv v.val) P.additive) -
          f 0 * additiveValueAtZero K S P.additive) := by
  have h := sIntegerPeriodicOrbitalPoisson K S Γ P.arithmetic.different_outside
    c hc ν μv μ P.additive.infiniteTest (finiteExtension K S P.additive)
    (finiteExtension_locallyConstant K S P.additive)
    (finiteExtension_compactSupport K S P.additive) f hinv d r
  dsimp only at h ⊢
  simpa only [weightedPhysicalOrbitalSeries, sIntegerWeightedOrbitalSeries,
    physicalPoissonScalar, ← additiveTest_eq_tensor K S P.additive,
    ← additiveFourier_eq_tensor K S μv P.additive,
    tensor_zero K S P.additive, dualTensor_zero K S μv P.additive] using h

end Expansion.PhysicalFourierNormalization

#print axioms Expansion.PhysicalFourierNormalization.additiveFourier_eq_tensor
#print axioms Expansion.PhysicalFourierNormalization.probePeriodicOrbitalPoisson
