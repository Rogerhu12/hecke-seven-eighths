import HeckeSkeleton.SmallRadius.ActualSLocalPositiveMoment
import HeckeSkeleton.SmallRadius.SLocalRadialMellinIntegral
import HeckeGeneral.Bridge.SLocalFiniteFourier
import HeckeGeneral.Bridge.TraceSchwartzFourier
import HeckeSkeleton.HighBinSupport.ActualDenominatorMellin

/-!
# Actual fixed Mellin factors on the small-row lines

The Fourier transform of the original additive test is an actual Schwartz
tensor: the archimedean factor is `traceSchwartzFourier`, and the finite
factor is the normalized finite-local Fourier profile.  Fourier closure
proves that the latter is locally constant and compactly supported.

The proved positive Mellin absolute moment, with the actual radial Haar
comparison scalar, makes the literal Fourier-weighted integral integrable.
Fubini then identifies it with `additiveMellin`.  Its norm is bounded on each
fixed positive Mellin line by the same absolute integral, independently of
the imaginary parameter.  No Mellin estimate or integrability property is
an input to the endpoint theorem.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SLocalRadialHaarDraft
open HeckeGeneral.Analysis.ActualSLocalPositiveMomentDraft
open NumberField.AdelicFourier NumberField.StandardAddChar
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K Sset

/-- Extend only the finite test outside its original index set; the actual
S-coordinates, all local measures, and all Fourier normalizers are retained. -/
def probeFiniteExtension (W : AdditiveProbeTest K Sset)
    (p : HeightOneSpectrum (𝓞 K)) : p.adicCompletion K → ℂ :=
  if hp : p ∈ S then W.finiteTest ⟨p, hp⟩ else 0

@[simp] theorem probeFiniteExtension_mem (W : AdditiveProbeTest K Sset) (p : Sset) :
    probeFiniteExtension K S W p.val = W.finiteTest p := by
  have hp : p.val ∈ S := p.property
  simp only [probeFiniteExtension, dif_pos hp]

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]

def additiveFourierFiniteProfile (W : AdditiveProbeTest K Sset) :
    ((p : Sset) → p.val.adicCompletion K) → ℂ :=
  sIntegerFiniteFourierTestFunction K S mu (probeFiniteExtension K S W)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu in
/-- Fourier closure is supplied by the actual adelic theorem, not by an
assumption on the transformed test. -/
theorem additiveFourierFiniteProfile_locallyConstant_compactSupport
    (W : AdditiveProbeTest K Sset) :
    IsLocallyConstant (additiveFourierFiniteProfile K S mu W) ∧
      HasCompactSupport (additiveFourierFiniteProfile K S mu W) := by
  apply sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S nu mu
    (probeFiniteExtension K S W)
  · intro p hp
    simpa only [probeFiniteExtension, dif_pos hp] using W.finite_locallyConstant ⟨p, hp⟩
  · intro p hp
    simpa only [probeFiniteExtension, dif_pos hp] using W.finite_compactSupport ⟨p, hp⟩

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- Exact tensor identity for the original Fourier transform. -/
theorem additiveFourier_eq_actual_tensor (W : AdditiveProbeTest K Sset) (x : G) :
    additiveFourier K Sset (fun p => mu p.val) W x =
      sLocalTensorTestFunction K Sset (traceSchwartzFourier K W.infiniteTest)
        (additiveFourierFiniteProfile K S mu W) x := by
  have harch :
      fourierIntegral (standardMixedAddCharacter K) volume
        (fun y => W.infiniteTest ((traceToMixed K).symm y))
        (x.1 : mixedEmbedding.mixedSpace K) =
          traceSchwartzFourier K W.infiniteTest
            ((traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K)) := by
    have hfunction :
        (traceSchwartzToMixed K W.infiniteTest : mixedEmbedding.mixedSpace K → ℂ) =
          fun y => W.infiniteTest ((traceToMixed K).symm y) := by
      funext y
      exact traceSchwartzToMixed_apply K W.infiniteTest y
    simpa only [hfunction, ContinuousLinearEquiv.apply_symm_apply] using
      fourierIntegral_traceSchwartzToMixed_traceToMixed K W.infiniteTest
        ((traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K))
  unfold additiveFourier sLocalTensorTestFunction additiveFourierFiniteProfile
    sIntegerFiniteFourierTestFunction
  rw [harch]
  simp only [probeFiniteExtension_mem]

-- These canonical Borel structures affect only the auxiliary genuine Haar
-- comparison, not the given norm-one or additive local measures.
local instance : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
local instance : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
local instance (p : Sset) : MeasurableSpace (p.val.adicCompletion K)ˣ := borel _
local instance (p : Sset) : BorelSpace (p.val.adicCompletion K)ˣ := ⟨rfl⟩

local instance : SecondCountableTopology (mixedEmbedding.mixedSpace K)ˣ := by
  letI : SecondCountableTopology (mixedEmbedding.mixedSpace K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance (p : Sset) : SecondCountableTopology (p.val.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

include nu in
/-- Both the actual weighted Fourier function and its additive Mellin
transform have uniform bounds on a fixed line with real part in (0,1]. -/
theorem exists_actual_additiveMellin_line_bound [IsTotallyComplex K]
    (W : AdditiveProbeTest K Sset) {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = sigma →
      Integrable
        (fun x : G => additiveFourier K Sset (fun p => mu p.val) W x *
          (sLocalProductNorm K Sset x : ℂ) ^ z)
        (sLocalRadialMeasure K Sset) ∧
      ‖additiveMellin K Sset (fun p => mu p.val) W z‖ ≤ C := by
  let phi : SchwartzMap V ℂ := traceSchwartzFourier K W.infiniteTest
  let psi := additiveFourierFiniteProfile K S mu W
  obtain ⟨hloc, hsupport⟩ :=
    additiveFourierFiniteProfile_locallyConstant_compactSupport K S mu nu W
  obtain ⟨indices, A, hA, hmoment⟩ := exists_radial_positive_moment_bound K Sset
    psi hloc.continuous hsupport sigma hsigma hsigma1
  let C : ℝ := A * indices.sup (schwartzSeminormFamily ℝ V ℂ) phi + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z hz
  let F : G → ℂ := fun x => additiveFourier K Sset (fun p => mu p.val) W x *
    (sLocalProductNorm K Sset x : ℂ) ^ z
  have hnorm (x : G) : ‖F x‖ = weightedTensorAbsolute K Sset phi psi sigma x := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (sLocalProductNorm_pos K Sset x), hz,
      additiveFourier_eq_actual_tensor K S mu W x]
    rfl
  have hcontinuous : Continuous F := by
    have hbase : Continuous (fun x : G => (sLocalProductNorm K Sset x : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_sLocalProductNorm K Sset)
    have hpow : Continuous (fun x : G => (sLocalProductNorm K Sset x : ℂ) ^ z) :=
      hbase.cpow continuous_const (fun x =>
        Complex.ofReal_mem_slitPlane.mpr (sLocalProductNorm_pos K Sset x))
    have hfourier : Continuous (fun x : G => additiveFourier K Sset (fun p => mu p.val) W x) := by
      simp_rw [additiveFourier_eq_actual_tensor K S mu W]
      exact continuous_sLocalTensorTestFunction K Sset phi psi hloc.continuous
    exact hfourier.mul hpow
  have hF : Integrable F (sLocalRadialMeasure K Sset) := by
    apply (hmoment phi).1.mono' hcontinuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => (hnorm x).le
  refine ⟨hF, ?_⟩
  calc
    ‖additiveMellin K Sset (fun p => mu p.val) W z‖ =
        ‖∫ x : G, F x ∂sLocalRadialMeasure K Sset‖ := by
      rw [additiveMellin_eq_integral_radialMeasure K Sset (fun p => mu p.val) W z hF]
    _ ≤ ∫ x : G, ‖F x‖ ∂sLocalRadialMeasure K Sset := norm_integral_le_integral_norm _
    _ = ∫ x : G, weightedTensorAbsolute K Sset phi psi sigma x
        ∂sLocalRadialMeasure K Sset := by simp_rw [hnorm]
    _ ≤ A * indices.sup (schwartzSeminormFamily ℝ V ℂ) phi := (hmoment phi).2
    _ ≤ C := le_add_of_nonneg_right zero_le_one

/-- The actual denominator transform on Re w=1/2 is uniformly bounded.
It uses the proved annular Mellin estimate with derivative order zero. -/
theorem exists_actual_denominatorMellin_small_line_bound (W : DenominatorTest) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re = 1 / 2 → ‖mellin W.toFun w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    W.toSmoothAnnularTest (1 / 2) (1 / 2) 0
  refine ⟨C, hC, ?_⟩
  intro w hw
  have heq : ((1 / 2 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = w := by
    apply Complex.ext <;> simp [hw]
  simpa only [pow_zero, one_mul, heq] using hb (1 / 2) w.im le_rfl le_rfl

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_additiveMellin_line_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_denominatorMellin_small_line_bound
