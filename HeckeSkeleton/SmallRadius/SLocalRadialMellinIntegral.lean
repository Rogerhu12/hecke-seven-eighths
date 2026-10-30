import HeckeSkeleton.SmallRadius.SLocalRadialHaarComparison
import HeckeGeneral.Analysis.PhysicalProbePrincipal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
Connect the literal physical additive Mellin integral to the actual radial
Haar measure. The only analytic hypothesis is integrability of the displayed
weighted Fourier function. No measure comparison identity is an input.
The exponential change of variable explicitly cancels its Jacobian with du/u.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SLocalRadialHaarDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton.Physical
open MeasureTheory MeasureTheory.Measure Set Topology
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
  [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))

/-- The actual exponential substitution, including the du/u Jacobian. -/
theorem additiveMellin_eq_log_integral (W : AdditiveProbeTest K S) (z : ℂ) :
    additiveMellin K S μ W z =
      ∫ r : ℝ,
        (∫ t : sLocalNormOneGroup K S,
          additiveFourier K S μ W
            ((t : sLocalMultiplicativeGroup K S) *
              sLocalNormSection K S ⟨Real.exp r, Real.exp_pos r⟩)
              ∂sUnitHaarMeasure K S) * (Real.exp r : ℂ) ^ z := by
  let g : ℝ → ℂ := fun u =>
    if hu : 0 < u then
      (∫ t : sLocalNormOneGroup K S,
        additiveFourier K S μ W
          ((t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨u, hu⟩)
            ∂sUnitHaarMeasure K S) * (u : ℂ) ^ z / (u : ℂ)
    else 0
  change (∫ u in Ioi (0 : ℝ), g u) = _
  rw [← integral_comp_exp g]
  apply integral_congr_ae
  filter_upwards [] with r
  dsimp only [g]
  rw [dif_pos (Real.exp_pos r), Complex.real_smul, ← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos r).ne')

-- Same literal Borel structure on the type-tagged log radius as the provider.
local instance : MeasurableSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasurableSpace ℝ)
local instance : BorelSpace (Multiplicative ℝ) := inferInstanceAs (BorelSpace ℝ)

variable [MeasurableSpace (sLocalMultiplicativeGroup K S)]
  [BorelSpace (sLocalMultiplicativeGroup K S)]

/-- Fubini is used only after proving integrability of the literal weighted
Fourier function on the actual transported Haar measure. -/
theorem additiveMellin_eq_integral_radialMeasure
    (W : AdditiveProbeTest K S) (z : ℂ)
    (hF : Integrable
      (fun x : sLocalMultiplicativeGroup K S =>
        additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z)
      (sLocalRadialMeasure K S)) :
    additiveMellin K S μ W z =
      ∫ x : sLocalMultiplicativeGroup K S,
        additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z
          ∂sLocalRadialMeasure K S := by
  let F : sLocalMultiplicativeGroup K S → ℂ := fun x =>
    additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z
  have hprod : Integrable
      (fun p : sLocalNormOneGroup K S × Multiplicative ℝ =>
        F (sLocalLogRadialEquiv K S p))
      ((sUnitHaarMeasure K S).prod logRadiusVolume) :=
    (sLocalLogRadialEquiv K S).toHomeomorph.measurableEmbedding.integrable_map_iff.mp hF
  rw [additiveMellin_eq_log_integral K S μ W z]
  change _ = ∫ x, F x ∂sLocalRadialMeasure K S
  rw [integral_sLocalRadialMeasure K S F, integral_prod_symm _ hprod]
  change _ = ∫ r : ℝ, ∫ t : sLocalNormOneGroup K S,
    F (sLocalLogRadialEquiv K S (t, Multiplicative.ofAdd r)) ∂sUnitHaarMeasure K S
  apply integral_congr_ae
  filter_upwards [] with r
  have heq : ∀ t : sLocalNormOneGroup K S,
      F (sLocalLogRadialEquiv K S (t, Multiplicative.ofAdd r)) =
        additiveFourier K S μ W
          ((t : sLocalMultiplicativeGroup K S) *
            sLocalNormSection K S ⟨Real.exp r, Real.exp_pos r⟩) *
          (Real.exp r : ℂ) ^ z := by
    intro t
    dsimp only [F]
    rw [productNorm_sLocalLogRadialEquiv, sLocalLogRadialEquiv_apply]
  simp_rw [heq]
  exact (integral_mul_const _ _).symm

/-- Full comparison with a genuine ambient Haar. The positive scalar is the
one computed by Haar uniqueness, and all local Fourier mass factors remain
inside the literal additiveFourier function. -/
theorem additiveMellin_eq_positiveScalar_mul_integral
    (ν : Measure (sLocalMultiplicativeGroup K S)) [ν.IsHaarMeasure]
    (W : AdditiveProbeTest K S) (z : ℂ)
    (hF : Integrable
      (fun x : sLocalMultiplicativeGroup K S =>
        additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z)
      (sLocalRadialMeasure K S)) :
    additiveMellin K S μ W z =
      ((radialHaarScalar K S ν : ℝ) : ℂ) *
        ∫ x : sLocalMultiplicativeGroup K S,
          additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z ∂ν := by
  rw [additiveMellin_eq_integral_radialMeasure K S μ W z hF]
  exact integral_sLocalRadialMeasure_eq_scalar_mul K S ν _

/-- Local-product integrability can be supplied directly on the target Haar;
the actual measure equality transports it to the radial measure. -/
theorem additiveMellin_eq_positiveScalar_mul_integral_of_integrable
    (ν : Measure (sLocalMultiplicativeGroup K S)) [ν.IsHaarMeasure]
    (W : AdditiveProbeTest K S) (z : ℂ)
    (hF : Integrable
      (fun x : sLocalMultiplicativeGroup K S =>
        additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z) ν) :
    additiveMellin K S μ W z =
      ((radialHaarScalar K S ν : ℝ) : ℂ) *
        ∫ x : sLocalMultiplicativeGroup K S,
          additiveFourier K S μ W x * (sLocalProductNorm K S x : ℂ) ^ z ∂ν := by
  apply additiveMellin_eq_positiveScalar_mul_integral K S μ ν W z
  rw [sLocalRadialMeasure_eq_smul K S ν]
  exact hF.smul_measure_nnreal

end HeckeGeneral.Analysis.SLocalRadialHaarDraft
