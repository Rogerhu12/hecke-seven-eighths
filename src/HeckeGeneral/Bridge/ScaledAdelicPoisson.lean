import HeckeGeneral.Bridge.FLTDefinitions
import HeckeGeneral.Bridge.SLocalIdeleAssembly
import FLTReuse.M791e48edf6c15dd6
import FLTReuse.M55886f866855a4cc
import FLTReuse.Mf2dfd7238df4aea9
import FLTReuse.M8a18b6fa749851ee

/-!
# Poisson summation at an actual idele dilation

The original Haar box normalization and the true idele modulus both remain
visible. Dilation preserves the actual Schwartz--Bruhat space, and the
Fourier change of variables is the proved adelic identity. No normalization
of Haar measure, determinant, or additive character is postulated.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain NumberField.AdelicFourier HeckeGeneral.Arithmetic
  NumberField.StandardAddChar HeckeGeneral.Characters MeasureTheory
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- Exact full-lattice Poisson under every genuine idele dilation. Both zero
terms are still present; their later separation must use actual summability. -/
theorem scaledAdelicPoisson
    (f : AdeleRing (𝓞 K) K → ℂ) (hf : f ∈ schwartzBruhat K)
    (u : IdeleGroup (𝓞 K) K) :
    (∑' a : K, f (u.val * algebraMap K (AdeleRing (𝓞 K) K) a)) =
      ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ * (idelicNorm K u : ℂ)⁻¹ *
        ∑' a : K, fourierIntegral (stdAddChar K) μ f
          ((u⁻¹).val * algebraMap K (AdeleRing (𝓞 K) K) a) := by
  have hg : (fun z : AdeleRing (𝓞 K) K => f (u.val * z)) ∈ schwartzBruhat K :=
    comp_mul_mem_schwartzBruhat K u hf
  have hmod : (distribHaarChar (AdeleRing (𝓞 K) K) u : ℝ) = idelicNorm K u :=
    fltIdeleNorm_eq K u
  rw [tsum_eq_inv_measure_mul_tsum_fourierIntegral K μ (isGlobalAddChar_stdAddChar K) hg]
  have htransform (w : AdeleRing (𝓞 K) K) :
      fourierIntegral (stdAddChar K) μ (fun z => f (u.val * z)) w =
        (idelicNorm K u : ℂ)⁻¹ * fourierIntegral (stdAddChar K) μ f ((u⁻¹).val * w) := by
    simpa only [hmod] using fourierIntegral_comp_mul_left K μ (stdAddChar K) f u w
  simp_rw [htransform]
  rw [tsum_mul_left, mul_assoc]

/-- On the actual positive-norm S-local slice, the dilation factor is exactly
the specified radius. It does not depend on the norm-one integration variable. -/
theorem sLocalScaledAdelicPoisson
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (f : AdeleRing (𝓞 K) K → ℂ) (hf : f ∈ schwartzBruhat K)
    (r : {r : ℝ // 0 < r}) (x : sLocalNormOneGroup K S) :
    (∑' a : K, f ((sLocalIdeleAssembly K S (sLocalNormSection K S r * x.val)).val *
      algebraMap K (AdeleRing (𝓞 K) K) a)) =
      ((μ (AdelicBox.adelicBox K)).toReal : ℂ)⁻¹ * (r.val : ℂ)⁻¹ *
        ∑' a : K, fourierIntegral (stdAddChar K) μ f
          (((sLocalIdeleAssembly K S (sLocalNormSection K S r * x.val))⁻¹).val *
            algebraMap K (AdeleRing (𝓞 K) K) a) := by
  have hx : sLocalProductNorm K S x.val = 1 :=
    (mem_sLocalNormOneGroup K S x.val).mp x.property
  have hnorm : idelicNorm K (sLocalIdeleAssembly K S
      (sLocalNormSection K S r * x.val)) = r.val := by
    rw [idelicNorm_sLocalIdeleAssembly, sLocalProductNorm_mul,
      sLocalProductNorm_section, hx, mul_one]
  simpa only [hnorm] using scaledAdelicPoisson K μ f hf
    (sLocalIdeleAssembly K S (sLocalNormSection K S r * x.val))

end HeckeGeneral.Bridge
