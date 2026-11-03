import ThetaGlobal.DeconvolverMoments
import ThetaGlobal.ConvolutionMass
import ThetaGlobal.GaussianTransfer

/-!
# Explicit arbitrary-test transfer from local Mellin pairs and a global seed

All scalar convolution, weighted-moment, absolute Fubini, and limit steps are
proved here. The one remaining global prerequisite is displayed as hseed:
equality of the two ACTUAL fixed-profile theta expansions at every log scale.
That prerequisite must be independently proved from the automorphic source.
This theorem is a conditional transfer theorem, not a claim to have supplied
the missing global automorphic identity.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.AnnularTransfer

open MeasureTheory Filter
open ScalarMellinConvolution DeconvolverMoments
open scoped Topology BigOperators

/-- Only local profile statements. In the application these are the actual
V0 and Hκ log profiles, their gamma Mellin pairs, and two-ended local bounds.
There is deliberately no global theta identity in this structure. -/
structure LocalProfiles (C : Type*) where
  direct : ℝ → ℂ
  reflected : C → ℝ → ℂ
  M : ℝ → ℂ
  R : C → ℝ → ℂ
  direct_continuous : Continuous direct
  reflected_continuous : ∀ c, Continuous (reflected c)
  direct_integrable : Integrable direct
  reflected_integrable : ∀ c, Integrable (reflected c)
  direct_mellin : ∀ t, positiveSpectrum direct t = M t
  reflected_mellin : ∀ c t, positiveSpectrum (reflected c) t = M (-t) * R c t
  M_ne_zero : ∀ t, M t ≠ 0
  exponent : ℝ
  directBound : ℝ
  reflectedBound : ℝ
  direct_tail : ∀ u, ‖direct u‖ ≤ directBound * Real.exp (-exponent * u)
  reflected_tail : ∀ c u, ‖reflected c u‖ ≤ reflectedBound * Real.exp (-exponent * u)

/-- A local scalar spectrum, not a theta seed. The intended spectrum is
Vhat(-w) exp(ε w²) times the actual entire reciprocal gamma product. -/
structure DeconvolverData (M Vhat : ℝ → ℂ) (ε : ℝ) where
  spectrum : ℂ → ℂ
  entire : Differentiable ℂ spectrum
  strip_decay : QuadraticStripDecay spectrum
  imaginary_line : ∀ t,
    verticalSpectrum spectrum 0 t = deconvolutionSpectrum M Vhat ε t

variable {C : Type*} (L : LocalProfiles C) (Vhat : ℝ → ℂ)

def kernel (ε : ℝ) (J : DeconvolverData L.M Vhat ε) : ℝ → ℂ :=
  logInverse J.spectrum 0

theorem kernel_continuous (ε : ℝ) (J : DeconvolverData L.M Vhat ε) :
    Continuous (kernel L Vhat ε J) :=
  continuous_logInverse J.entire J.strip_decay

theorem kernel_moment (ε : ℝ) (J : DeconvolverData L.M Vhat ε) (q : ℝ) :
    Integrable (fun u => ‖kernel L Vhat ε J u‖ * Real.exp (q * u)) :=
  integrable_log_power_moment J.entire J.strip_decay q

theorem deconvolution_spectrum_integrable (ε : ℝ)
    (J : DeconvolverData L.M Vhat ε) :
    Integrable (deconvolutionSpectrum L.M Vhat ε) := by
  have heq : verticalSpectrum J.spectrum 0 = deconvolutionSpectrum L.M Vhat ε :=
    funext J.imaginary_line
  rw [← heq]
  exact integrable_verticalSpectrum J.entire J.strip_decay 0

theorem kernel_eq_scalar (ε : ℝ) (J : DeconvolverData L.M Vhat ε) (u : ℝ) :
    kernel L Vhat ε J u =
      ScalarMellinConvolution.inverseLine (deconvolutionSpectrum L.M Vhat ε) u := by
  unfold kernel
  rw [zeroLine_eq_scalarInverse]
  congr 1
  exact funext J.imaginary_line

theorem direct_scalar_convolution (ε : ℝ) (J : DeconvolverData L.M Vhat ε)
    (a : ℂ) (x : ℝ) :
    (∫ u, kernel L Vhat ε J u * (a * L.direct (u + x))) =
      a * regularizedTest Vhat ε x := by
  calc
    _ = a * ∫ u, kernel L Vhat ε J u * L.direct (u + x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = _ := by
      simp_rw [kernel_eq_scalar]
      rw [deconvolver_direct L.direct L.direct_integrable L.M Vhat ε
        L.direct_mellin L.M_ne_zero (deconvolution_spectrum_integrable L Vhat ε J)]

theorem reflected_scalar_convolution (ε : ℝ) (J : DeconvolverData L.M Vhat ε)
    (b : ℂ) (c : C) (x : ℝ) :
    (∫ u, kernel L Vhat ε J u * (b * L.reflected c (x - u))) =
      b * regularizedReflected Vhat (L.R c) ε x := by
  calc
    _ = b * ∫ u, kernel L Vhat ε J u * L.reflected c (x - u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = _ := by
      simp_rw [kernel_eq_scalar]
      rw [deconvolver_reflected (L.reflected c) (L.reflected_integrable c)
        L.M Vhat (L.R c) ε (L.reflected_mellin c) L.M_ne_zero
        (deconvolution_spectrum_integrable L Vhat ε J)]

variable {I J : Type*} [Countable I] [Countable J]

/-- Every integral/sum interchange is proved from the local spectral moments,
local profile tails, and independently proved arithmetic norm majorants.
hseed is precisely the independent global automorphic prerequisite. -/
theorem regularized_reflection
    (a : I → ℂ) (b : J → ℂ) (x : I → ℝ) (y : J → ℝ) (sector : J → C)
    (ha : Summable (fun i => ‖a i‖ * Real.exp (-L.exponent * x i)))
    (hb : Summable (fun j => ‖b j‖ * Real.exp (-L.exponent * y j)))
    (hseed : ∀ u : ℝ, (∑' i, a i * L.direct (u + x i)) =
      ∑' j, b j * L.reflected (sector j) (y j - u))
    (ε : ℝ) (D : DeconvolverData L.M Vhat ε) :
    (∑' i, a i * regularizedTest Vhat ε (x i)) =
      ∑' j, b j * regularizedReflected Vhat (L.R (sector j)) ε (y j) := by
  have hd := ConvolutionMass.direct_convolution_absolute_mass
    L.direct (kernel L Vhat ε D) a x L.exponent L.directBound L.direct_tail ha
    (kernel_moment L Vhat ε D (-L.exponent)) (by
      intro i
      exact ((kernel_continuous L Vhat ε D).mul
        (continuous_const.mul (L.direct_continuous.comp (by fun_prop)))).aestronglyMeasurable)
  have hr := ConvolutionMass.reflected_convolution_absolute_mass
    (fun j => L.reflected (sector j)) (kernel L Vhat ε D) b y
    L.exponent L.reflectedBound (fun j => L.reflected_tail (sector j)) hb
    (kernel_moment L Vhat ε D L.exponent) (by
      intro j
      exact ((kernel_continuous L Vhat ε D).mul
        (continuous_const.mul ((L.reflected_continuous (sector j)).comp
          (by fun_prop)))).aestronglyMeasurable)
  exact GaussianTransfer.regularized_identity
    (fun i u => a i * L.direct (u + x i))
    (fun j u => b j * L.reflected (sector j) (y j - u))
    (kernel L Vhat ε D)
    (fun i => a i * regularizedTest Vhat ε (x i))
    (fun j => b j * regularizedReflected Vhat (L.R (sector j)) ε (y j))
    (Eventually.of_forall hseed) hd.1 hr.1 hd.2 hr.2
    (fun i => direct_scalar_convolution L Vhat ε D (a i) (x i))
    (fun j => reflected_scalar_convolution L Vhat ε D (b j) (sector j) (y j))

/-- Arbitrary-test transfer with no assumed scalar convolution or summed
regularized identity. The remaining assumptions are local scalar limits and
uniform tails, arithmetic majorants, and the explicit fixed-profile seed. -/
theorem arbitrary_test_reflection
    (a : I → ℂ) (b : J → ℂ) (x : I → ℝ) (y : J → ℝ) (sector : J → C)
    (ha : Summable (fun i => ‖a i‖ * Real.exp (-L.exponent * x i)))
    (hb : Summable (fun j => ‖b j‖ * Real.exp (-L.exponent * y j)))
    (hseed : ∀ u : ℝ, (∑' i, a i * L.direct (u + x i)) =
      ∑' j, b j * L.reflected (sector j) (y j - u))
    (ε : ℕ → ℝ) (D : ∀ n, DeconvolverData L.M Vhat (ε n))
    (V : ℝ → ℂ) (Phi : C → ℝ → ℂ)
    (hV : ∀ z, Tendsto (fun n => regularizedTest Vhat (ε n) z) atTop (𝓝 (V z)))
    (hPhi : ∀ c z, Tendsto (fun n => regularizedReflected Vhat (L.R c) (ε n) z)
      atTop (𝓝 (Phi c z)))
    (CV CPhi : ℝ)
    (hVtail : ∀ n z, ‖regularizedTest Vhat (ε n) z‖ ≤
      CV * Real.exp (-L.exponent * z))
    (hPhitail : ∀ n c z, ‖regularizedReflected Vhat (L.R c) (ε n) z‖ ≤
      CPhi * Real.exp (-L.exponent * z)) :
    Summable (fun i => a i * V (x i)) ∧
      Summable (fun j => b j * Phi (sector j) (y j)) ∧
      (∑' i, a i * V (x i)) = ∑' j, b j * Phi (sector j) (y j) := by
  apply GaussianTransfer.remove_regularizer
    (fun n i => a i * regularizedTest Vhat (ε n) (x i))
    (fun n j => b j * regularizedReflected Vhat (L.R (sector j)) (ε n) (y j))
    (fun i => a i * V (x i)) (fun j => b j * Phi (sector j) (y j))
    (fun i => (‖a i‖ * Real.exp (-L.exponent * x i)) * CV)
    (fun j => (‖b j‖ * Real.exp (-L.exponent * y j)) * CPhi)
    (ha.mul_right CV) (hb.mul_right CPhi)
  · intro i
    exact tendsto_const_nhds.mul (hV (x i))
  · intro j
    exact tendsto_const_nhds.mul (hPhi (sector j) (y j))
  · intro n i
    rw [norm_mul]
    calc
      _ ≤ ‖a i‖ * (CV * Real.exp (-L.exponent * x i)) :=
        mul_le_mul_of_nonneg_left (hVtail n (x i)) (norm_nonneg _)
      _ = _ := by ring
  · intro n j
    rw [norm_mul]
    calc
      _ ≤ ‖b j‖ * (CPhi * Real.exp (-L.exponent * y j)) :=
        mul_le_mul_of_nonneg_left (hPhitail n (sector j) (y j)) (norm_nonneg _)
      _ = _ := by ring
  · intro n
    exact regularized_reflection L Vhat a b x y sector ha hb hseed (ε n) (D n)

end ThetaGlobal.AnnularTransfer

