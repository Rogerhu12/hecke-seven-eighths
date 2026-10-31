import Expansion.PhysicalPositiveMellinInversion
import Expansion.PhysicalInitialHeight
import Expansion.PhysicalInitialPowers
import HeckeGeneral.Analysis.GaussianContour
import HeckeGeneral.Analysis.IdealDerivativeSmoothing
import HeckeSkeleton.HighBinSupport.ActualNormFormMellinInversion

/-!
# The three actual inverse Mellin transforms

The independent lines are a=7, w=5 and z=3.  Their product is an
absolutely integrable three-dimensional inverse transform.  The shear
a=s+z-1 then gives the initial physical lines (s,w,z)=(5,5,3).
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open Expansion.PhysicalPositiveMellin Expansion.PhysicalInitialHeight
open HighBinVerified.NormFormMellin
open scoped Classical BigOperators Topology

def tripleMellinConstant : ℂ := (2 * (Real.pi : ℂ))⁻¹ ^ 3

def inverseMellinKernel (F : ℂ → ℂ) (σ x t : ℝ) : ℂ :=
  F (idealVerticalPoint σ t) * (x : ℂ) ^ (-idealVerticalPoint σ t)

theorem integrable_inverseMellinKernel (F : ℂ → ℂ) (σ : ℝ)
    (hF : Complex.VerticalIntegrable F σ) {x : ℝ} (hx : 0 < x) :
    Integrable (inverseMellinKernel F σ x) := by
  apply hF.mul_bdd
  · exact ((continuous_idealVerticalPoint σ).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re, idealVerticalPoint_re])

theorem normalized_inverseMellinKernel (F : ℂ → ℂ) (σ x : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, inverseMellinKernel F σ x t = mellinInv σ F x := by
  simp only [mellinInv, inverseMellinKernel, idealVerticalPoint, Complex.real_smul,
    smul_eq_mul, one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_comm]

theorem gaussian_mellin_inversion (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s : ℂ => Complex.exp (s ^ 2)) x = logGaussianProfile x := by
  have hv : Complex.VerticalIntegrable (mellin logGaussianProfile) σ := by
    simpa only [mellin_logGaussianProfile, gaussianContourFactor, sub_zero] using
      verticalIntegrable_gaussianContourFactor 0 σ
  have hc : ContinuousAt logGaussianProfile x := by
    unfold logGaussianProfile logarithmicGaussian
    fun_prop (disch := exact hx.ne')
  have h := mellinInv_mellin_eq σ logGaussianProfile hx
    (mellinConvergent_logGaussianProfile (σ : ℂ)) hv hc
  simpa only [mellin_logGaussianProfile] using h

theorem verticalIntegrable_gaussianMellin (σ : ℝ) :
    Complex.VerticalIntegrable (fun s : ℂ => Complex.exp (s ^ 2)) σ := by
  simpa only [gaussianContourFactor, sub_zero] using
    verticalIntegrable_gaussianContourFactor 0 σ

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K Sset)] [BorelSpace (sLocalNormOneGroup K Sset)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem continuous_physical_additiveMellin_line (W : AdditiveProbeTest K Sset)
    (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ =>
      additiveMellin K Sset (fun v => μv v.val) W (idealVerticalPoint σ t)) := by
  have hft := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv
    (Expansion.PhysicalFourierNormalization.finiteExtension K S W)
    (Expansion.PhysicalFourierNormalization.finiteExtension_locallyConstant K S W)
    (Expansion.PhysicalFourierNormalization.finiteExtension_compactSupport K S W)
  simp_rw [physical_additiveMellin_eq_orbital K S μv W]
  exact continuous_orbitalMellin_positive_line K Sset (⊤ : Subgroup (Sset.unit K))
    (traceSchwartzFourier K W.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S μv
      (Expansion.PhysicalFourierNormalization.finiteExtension K S W))
    hft.1.continuous hft.2 σ hσ

include ν in
theorem verticalIntegrable_physical_additiveMellin (W : AdditiveProbeTest K Sset)
    (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (additiveMellin K Sset (fun v => μv v.val) W) σ := by
  have hft := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv
    (Expansion.PhysicalFourierNormalization.finiteExtension K S W)
    (Expansion.PhysicalFourierNormalization.finiteExtension_locallyConstant K S W)
    (Expansion.PhysicalFourierNormalization.finiteExtension_compactSupport K S W)
  have heq : additiveMellin K Sset (fun v => μv v.val) W =
      HighBinBoundary.ActualOrbital.orbitalMellin K Sset
        (traceSchwartzFourier K W.infiniteTest)
        (sIntegerFiniteFourierTestFunction K S μv
          (Expansion.PhysicalFourierNormalization.finiteExtension K S W)) :=
    funext (physical_additiveMellin_eq_orbital K S μv W)
  rw [heq]
  exact verticalIntegrable_orbitalMellin_positive K Sset (⊤ : Subgroup (Sset.unit K))
    (traceSchwartzFourier K W.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S μv
      (Expansion.PhysicalFourierNormalization.finiteExtension K S W))
    hft.1.continuous hft.2 σ hσ

def tripleProfileKernel (P : ProbeData K Sset) (L D R : ℝ) (t : Fin 3 → ℝ) : ℂ :=
  inverseMellinKernel (fun s : ℂ => Complex.exp (s ^ 2)) 7 L (t 0) *
    inverseMellinKernel (mellin P.denominator.toFun) 5 D (t 1) *
    inverseMellinKernel (additiveMellin K Sset (fun v => μv v.val) P.additive) 3 R (t 2)

include ν in
theorem integrable_tripleProfileKernel (P : ProbeData K Sset) (L D R : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hR : 0 < R) :
    Integrable (tripleProfileKernel K S μv P L D R) :=
  integrable_three_product
    (integrable_inverseMellinKernel _ 7 (verticalIntegrable_gaussianMellin 7) hL)
    (integrable_inverseMellinKernel _ 5
      (verticalIntegrable_mellin P.denominator.toSmoothAnnularTest 5) hD)
    (integrable_inverseMellinKernel _ 3
      (verticalIntegrable_physical_additiveMellin K S μv ν P.additive 3 (by norm_num)) hR)

include ν in
theorem three_profiles_mellin_inversion (P : ProbeData K Sset) (L D R : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hR : 0 < R) :
    logGaussianProfile L * P.denominator.toFun D *
        sUnitOrbitalProfile K Sset
          (additiveFourier K Sset (fun v => μv v.val) P.additive) ⟨R, hR⟩ =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ, tripleProfileKernel K S μv P L D R t := by
  have hG := (normalized_inverseMellinKernel (fun s : ℂ => Complex.exp (s ^ 2)) 7 L).trans
    (gaussian_mellin_inversion 7 hL)
  have hD' := (normalized_inverseMellinKernel (mellin P.denominator.toFun) 5 D).trans
    (mellin_inversion_annular P.denominator.toSmoothAnnularTest 5 hD)
  have hR' := (normalized_inverseMellinKernel
    (additiveMellin K Sset (fun v => μv v.val) P.additive) 3 R).trans
      (physical_additiveMellin_inversion K S μv ν P.additive 3 (by norm_num) hR)
  rw [← hG, ← hD', ← hR']
  unfold tripleProfileKernel
  rw [integral_three_product]
  unfold tripleMellinConstant
  ring

include ν in
theorem three_profiles_mellin_inversion_sheared (P : ProbeData K Sset) (L D R : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hR : 0 < R) :
    logGaussianProfile L * P.denominator.toFun D *
        sUnitOrbitalProfile K Sset
          (additiveFourier K Sset (fun v => μv v.val) P.additive) ⟨R, hR⟩ =
      tripleMellinConstant *
        ∫ t : Fin 3 → ℝ, tripleProfileKernel K S μv P L D R (heightShear t) := by
  rw [integral_heightShear]
  exact three_profiles_mellin_inversion K S μv ν P L D R hL hD hR

theorem initial_shear_line (t : Fin 3 → ℝ) :
    idealVerticalPoint 7 ((heightShear t) 0) =
      idealVerticalPoint 5 (t 0) + idealVerticalPoint 3 (t 2) - 1 := by
  simp only [idealVerticalPoint, heightShear, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
    Matrix.cons_val_zero, Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.three_profiles_mellin_inversion_sheared
