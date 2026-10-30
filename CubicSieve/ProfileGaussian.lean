import CubicSieve.Profile
import DedekindZetaZeroFree.Theta.Profiles.MixedGaussian
import DedekindZetaZeroFree.Theta.Unfolding.RayParityProductMellin
import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalCosetIndicators
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import HeckeGeneral.Bridge.SLocalFiniteFourier

/-! The actual Gaussian smoothing test. Its archimedean Schwartz function is
the already proved trace Gaussian, and its finite test is the same unit shell.
The Gaussian is positive at zero and therefore can smooth the whole norm ball. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CubicSieve.Profile.Gaussian

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Bridge MeasureTheory
open scoped Classical NumberField

variable (K : Type) [Field K] [NumberField K]

def archTest : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ :=
  AbelianQuotient.Theta.traceGaussianSchwartz K

theorem archTest_apply (x : mixedEmbedding.euclidean.mixedSpace K) :
    archTest K x = AbelianQuotient.Theta.latticeGaussian Real.pi x :=
  AbelianQuotient.Theta.traceGaussianSchwartz_apply K x

variable {K} (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))

def originalLocalFunction : sLocalMultiplicativeGroup K S → ℂ :=
  sLocalTensorTestFunction K S (archTest K) (Profile.finiteTest A)

local instance profilegaussianLocalInstance1 (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (v.adicCompletion K) := borel _
local instance profilegaussianLocalInstance2 (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance profilegaussianLocalInstance3 : MeasurableSpace (SLocalProduct K A.Sf) := borel _
local instance profilegaussianLocalInstance4 : BorelSpace (SLocalProduct K A.Sf) := ⟨rfl⟩
local instance profilegaussianLocalInstance5 : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance profilegaussianLocalInstance6 : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩

def originalTest (x : SLocalProduct K A.Sf) : ℂ :=
  archTest K ((traceToMixed K).symm ((InfiniteAdeleRing.ringEquiv_mixedSpace K) x.1)) *
    Profile.finiteTest A x.2

theorem originalTest_at_units (x : sLocalMultiplicativeGroup K S) :
    originalTest A (HeckeAxiom.ProbeUnits.toUnits A x).val = originalLocalFunction A x := by
  unfold originalTest originalLocalFunction sLocalTensorTestFunction
  rw [HeckeAxiom.ProbeUnits.val_toUnits, RingEquiv.apply_symm_apply]
  rfl

def complexTest : SchwartzMap ℂ ℂ :=
  Classical.choose (AbelianQuotient.Theta.exists_latticeGaussianSchwartz
    (E := ℂ) (2 * Real.pi) (by positivity))

theorem complexTest_apply (z : ℂ) :
    complexTest z = AbelianQuotient.Theta.latticeGaussian (2 * Real.pi) z :=
  Classical.choose_spec (AbelianQuotient.Theta.exists_latticeGaussianSchwartz
    (E := ℂ) (2 * Real.pi) (by positivity)) z

private theorem traceToMixed_eq :
    AbelianQuotient.Theta.traceToMixed K = HeckeGeneral.Arithmetic.traceToMixed K := by
  rfl

include A in
theorem archTest_factor (m : mixedEmbedding.mixedSpace K) :
    archTest K ((traceToMixed K).symm m) =
      ∏ v : {v : InfinitePlace K // v.IsComplex}, complexTest (m.2 v) := by
  haveI : IsEmpty {v : InfinitePlace K // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.val)) v.property⟩
  simp_rw [complexTest_apply]
  rw [archTest_apply, AbelianQuotient.Theta.latticeGaussian, ← Complex.ofReal_pow,
    AbelianQuotient.RayParity.norm_sq_traceToMixed, traceToMixed_eq]
  simp only [ContinuousLinearEquiv.apply_symm_apply, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add]
  simp only [AbelianQuotient.Theta.latticeGaussian]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  push_cast
  ring

theorem fourier_archTest (y : mixedEmbedding.euclidean.mixedSpace K) :
    FourierTransform.fourier (archTest K : mixedEmbedding.euclidean.mixedSpace K → ℂ) y =
      archTest K y := by
  have heq : (archTest K : mixedEmbedding.euclidean.mixedSpace K → ℂ) =
      fun x => Complex.exp (-(Real.pi : ℂ) * ‖x‖ ^ 2) := by
    funext x
    rw [archTest_apply]
    simp [AbelianQuotient.Theta.latticeGaussian]
  rw [heq, fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [div_self hπ, Complex.one_cpow, one_mul]
  congr 1
  field_simp
  <;> ring

theorem traceFourier_archTest (y : mixedEmbedding.euclidean.mixedSpace K) :
    traceSchwartzFourier K (archTest K) y =
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K)⁻¹ : ℂ) * archTest K y := by
  have hg : archTest K (traceConjugation K y) = archTest K y := by
    rw [archTest_apply, archTest_apply]
    unfold AbelianQuotient.Theta.latticeGaussian
    rw [(traceConjugation K).norm_map]
  rw [traceSchwartzFourier_apply, fourier_archTest, hg]
  simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]

def finiteFourier (v : ↥A.Sf) : v.val.adicCompletion K → ℂ :=
  localFourierIntegral K v.val (TateFiniteShell.annularTest K v.val)

theorem finiteFourier_regular (v : ↥A.Sf) :
    IsLocallyConstant (finiteFourier A v) ∧ HasCompactSupport (finiteFourier A v) := by
  let B := fun n : ℤ => TateFiniteShell.ballTest K v.val n
  let C := fun n : ℤ => localCosetIndicator K v.val 0
    (finiteCompletionBall K v.val (-n - (localDifferentExponent K v.val : ℤ)))
  have hC (n : ℤ) : C n ∈ localSchwartz K v.val :=
    localCosetIndicator_mem_localSchwartz K v.val _
      (isCompact_finiteCompletionBall K v.val _) (isOpen_finiteCompletionBall K v.val _) 0
  have hb (n : ℤ) : B n = localCosetIndicator K v.val 0 (finiteCompletionBall K v.val n) := by
    funext x
    simp [B, TateFiniteShell.ballTest, localCosetIndicator_apply, Set.indicator]
  have hfb (n : ℤ) (y : v.val.adicCompletion K) :
      localFourierIntegral K v.val (B n) y = (localBallMass K v.val n : ℂ) * C n y := by
    rw [hb n, localFourierIntegral_localCosetIndicator_ball]
    simp [C]
  have heq : finiteFourier A v = fun y =>
      (localBallMass K v.val 0 : ℂ) * C 0 y - (localBallMass K v.val 1 : ℂ) * C 1 y := by
    funext y
    unfold finiteFourier
    rw [localFourierIntegral_apply, TateFiniteShell.annularTest_eq_sub]
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub
      (TateFiniteShell.fourier_ballTestIntegrand_integrable K v.val _
        (continuous_localFiniteCharacter K v.val) (localNormalizedHaar K v.val) 0 y)
      (TateFiniteShell.fourier_ballTestIntegrand_integrable K v.val _
        (continuous_localFiniteCharacter K v.val) (localNormalizedHaar K v.val) 1 y)]
    rw [← localFourierIntegral_apply K v.val (TateFiniteShell.ballTest K v.val 0) y,
      ← localFourierIntegral_apply K v.val (TateFiniteShell.ballTest K v.val 1) y]
    rw [hfb 0 y, hfb 1 y]
  rw [heq]
  exact ⟨((IsLocallyConstant.const _).mul (hC 0).1).sub
      ((IsLocallyConstant.const _).mul (hC 1).1),
    ((hC 0).2.mul_left).sub ((hC 1).2.mul_left)⟩

def finiteFourierProduct (x : (v : ↥A.Sf) → v.val.adicCompletion K) : ℂ :=
  ∏ v, finiteFourier A v (x v)

theorem finiteFourierProduct_continuous : Continuous (finiteFourierProduct A) := by
  apply continuous_finsetProd
  intro v _
  exact (finiteFourier_regular A v).1.continuous.comp (continuous_apply v)

theorem finiteFourierProduct_compactSupport : HasCompactSupport (finiteFourierProduct A) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun v =>
    (finiteFourier_regular A v).2.isCompact) fun x hx => ?_
  simp only [Set.mem_univ_pi, not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ v)
    (image_eq_zero_of_notMem_tsupport (f := finiteFourier A v) hv)

def canonicalFourier : SLocalProduct K A.Sf → ℂ :=
  ProbeWeight.fourier K A.Sf (Profile.canonicalCharacters A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A) (originalTest A)

theorem canonical_local_fourier (v : ↥A.Sf) (y : v.val.adicCompletion K) :
    NumberField.AdelicFourier.fourierIntegral (NumberField.StandardAddChar.psiLocal K v.val)
      (HeckeAxiom.ProbeTestChoice.localHaar A v) (TateFiniteShell.annularTest K v.val) y =
        finiteFourier A v y := by
  rw [NumberField.AdelicFourier.fourierIntegral_def, finiteFourier, localFourierIntegral_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [HeckeAxiom.TraceDictionary.psiLocal_eq_localTraceCharacter,
      CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter]
    rw [neg_mul]
    ring

theorem canonicalFourier_factor (y : SLocalProduct K A.Sf) :
    canonicalFourier A y =
      archTest K ((traceToMixed K).symm ((InfiniteAdeleRing.ringEquiv_mixedSpace K) y.1)) *
        finiteFourierProduct A y.2 := by
  letI (v : ↥A.Sf) : SigmaFinite (HeckeAxiom.ProbeTestChoice.localHaar A v) :=
    HeckeAxiom.ProbeTestChoice.sigmaFinite_localHaar A v
  have hchar (v : ↥A.Sf) (z : v.val.adicCompletion K) :
      (Profile.canonicalCharacters A v z : ℂ) = NumberField.StandardAddChar.psiLocal K v.val z :=
    (HeckeAxiom.TraceDictionary.psiLocal_eq_localTraceCharacter v.val z).symm
  have heq := HeckeAxiom.ProbeFourier.fourier_eq A (Profile.canonicalCharacters A) hchar
    (HeckeAxiom.ProbeTestChoice.localHaar A) (traceSchwartzToMixed K (archTest K))
    (fun v => TateFiniteShell.annularTest K v.val) (originalTest A) (fun _ => rfl) y
  change canonicalFourier A y = _ at heq
  have harch := fourierIntegral_traceSchwartzToMixed_traceToMixed K (archTest K)
    ((traceToMixed K).symm ((InfiniteAdeleRing.ringEquiv_mixedSpace K) y.1))
  rw [ContinuousLinearEquiv.apply_symm_apply] at harch
  rw [harch, traceFourier_archTest] at heq
  have hfin (v : ↥A.Sf) :
      NumberField.AdelicFourier.fourierIntegral (NumberField.StandardAddChar.psiLocal K v.val)
        (HeckeAxiom.ProbeTestChoice.localHaar A v) (TateFiniteShell.annularTest K v.val) (y.2 v) =
          finiteFourier A v (y.2 v) := canonical_local_fourier A v (y.2 v)
  simp_rw [hfin] at heq
  rw [heq]
  unfold finiteFourierProduct
  have hscalar : (PoissonArch.haarScalar K : ℂ) *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K)⁻¹ : ℂ) = 1 := by
    simp [PoissonArch.haarScalar, Complex.ofReal_pow]
  calc
    _ = ((PoissonArch.haarScalar K : ℂ) *
        (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K)⁻¹ : ℂ)) *
        (archTest K ((traceToMixed K).symm ((InfiniteAdeleRing.ringEquiv_mixedSpace K) y.1)) *
          ∏ v, finiteFourier A v (y.2 v)) := by ring
    _ = _ := by rw [hscalar, one_mul]

theorem canonicalFourier_isSchwartzTensor :
    ProbeSheetVerticalDecay.IsSchwartzTensor K A.Sf (canonicalFourier A) := by
  haveI : IsEmpty {v : InfinitePlace K // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.val)) v.property⟩
  refine ⟨1, fun _ => 0, fun _ => complexTest, finiteFourier A,
    finiteFourier_regular A, ?_⟩
  intro x
  rw [canonicalFourier_factor A x, archTest_factor A]
  simp [finiteFourierProduct]

def dualLocalFunction (x : sLocalMultiplicativeGroup K S) : ℂ :=
  canonicalFourier A (HeckeAxiom.ProbeUnits.toUnits A x).val

theorem dualLocalFunction_eq_tensor : dualLocalFunction A =
    sLocalTensorTestFunction K S (archTest K) (finiteFourierProduct A) := by
  funext x
  rw [dualLocalFunction, canonicalFourier_factor]
  unfold sLocalTensorTestFunction
  rw [HeckeAxiom.ProbeUnits.val_toUnits, RingEquiv.apply_symm_apply]
  rfl

/-- The normalization in the actual Poisson consumer is retained explicitly.
The canonical Fourier tensor differs by precisely the existing scalar kappa. -/
theorem physicalDual_eq_kappa (x : sLocalMultiplicativeGroup K S) :
    sLocalTensorTestFunction K S (traceSchwartzFourier K (archTest K))
      (sIntegerFiniteFourierTestFunction K A.Sf (localNormalizedHaar K)
        (fun v => TateFiniteShell.annularTest K v)) x =
      HeckeAxiom.ProbeTestChoice.kappa A * dualLocalFunction A x := by
  rw [dualLocalFunction_eq_tensor]
  unfold sLocalTensorTestFunction sIntegerFiniteFourierTestFunction finiteFourierProduct
  rw [traceFourier_archTest]
  have hlocal (v : ↥A.Sf) :
      NumberField.AdelicFourier.fourierIntegral (NumberField.StandardAddChar.psiLocal K v.val)
        (localNormalizedHaar K v.val) (TateFiniteShell.annularTest K v.val)
        (x.2 v).val =
          finiteFourier A v (x.2 v).val := canonical_local_fourier A v _
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  unfold HeckeAxiom.ProbeTestChoice.kappa PoissonArch.haarScalar
  dsimp only [HeckeAxiom.selfDualProbeMeasures]
  (try simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]) <;> ring <;> rfl

end CubicSieve.Profile.Gaussian
