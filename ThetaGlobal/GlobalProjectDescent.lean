import ThetaGlobal.GlobalCoreSource
import ThetaGlobal.GlobalFourierDescent

/-!
# Actual residual-vector rational Fourier descent

This adapter applies the checked analytic assembly theorem to the
upstream residual module, its actual trace-character Fourier periods,
its actual upper constant term, and its rational Weyl element.

The resulting equality is over rational nonzero frequencies, before
unfolding the unit orbit and evaluating local factors.  It is therefore
usable for high K-type vectors in the same residual realization without
assuming any marked reflection identity.  The displayed integrability
hypotheses are the precise analytic estimates still required to use the
adapter for a chosen period.

This is a project-facing module; see the separate compilation-status report.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectDescent

open DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open NumberField MeasureTheory
open scoped NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
  (T : Realization R Q)
  {X E : Type*} [MeasurableSpace X] [Fintype E]

/-- A weighted, finite-digit-averaged actual rational Fourier coefficient. -/
def coefficientIntegral (μ : Measure X) (f : sameResidueModule T)
    (weight : X → ℂ) (digit : E → ℂ) (g : E → X → Group R) (a : Fˣ) : ℂ :=
  ∫ x, weight x * ∑ d, digit d *
    GlobalCoreSource.rationalPeriod T f (a : F) (g d x) ∂μ

/-- The rational Weyl symmetry becomes equality of the integrated
nonzero-frequency series for the actual residual vector. -/
theorem actual_rational_fourier_descent
    (μ : Measure X) (f : sameResidueModule T)
    (weight : X → ℂ) (digit : E → ℂ) (g : E → X → Group R)
    (hs₀ : ∀ d x, Summable (fun a : F =>
      ‖GlobalCoreSource.rationalPeriod T f a (g d x)‖))
    (hs₁ : ∀ d x, Summable (fun a : F =>
      ‖GlobalCoreSource.rationalPeriod T f a
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x)‖))
    (ha : ∀ a : Fˣ, Integrable (fun x => weight x * ∑ d, digit d *
      GlobalCoreSource.rationalPeriod T f (a : F) (g d x)) μ)
    (ha_norm : Summable (fun a : Fˣ => ∫ x, ‖weight x * ∑ d, digit d *
      GlobalCoreSource.rationalPeriod T f (a : F) (g d x)‖ ∂μ))
    (hb : ∀ a : Fˣ, Integrable (fun x => weight x * ∑ d, digit d *
      GlobalCoreSource.rationalPeriod T f (a : F)
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x)) μ)
    (hb_norm : Summable (fun a : Fˣ => ∫ x, ‖weight x * ∑ d, digit d *
      GlobalCoreSource.rationalPeriod T f (a : F)
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x)‖ ∂μ))
    (hθ : Integrable (fun x => weight x * ∑ d, digit d * f.val (g d x)) μ)
    (hc₀ : Integrable (fun x => weight x * ∑ d, digit d *
      upper R Q.dq f.val (g d x)) μ)
    (hc₁ : Integrable (fun x => weight x * ∑ d, digit d *
      upper R Q.dq f.val
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x)) μ)
    (hc₀_zero : (∫ x, weight x * ∑ d, digit d *
      upper R Q.dq f.val (g d x) ∂μ) = 0)
    (hc₁_zero : (∫ x, weight x * ∑ d, digit d *
      upper R Q.dq f.val
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x) ∂μ) = 0) :
    (∑' a : Fˣ, coefficientIntegral T μ f weight digit g a) =
      ∑' a : Fˣ, coefficientIntegral T μ f weight digit
        (fun d x =>
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x) a := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable Fˣ := Function.Injective.countable (f := ((↑) : Fˣ → F)) fun _ _ h => Units.ext h
  exact GlobalFourierDescent.integrated_finite_average_weyl
    μ weight f.val
    (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)
    digit g (GlobalCoreSource.weyl T f)
    (fun d x => upper R Q.dq f.val (g d x))
    (fun d x => upper R Q.dq f.val
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x))
    (fun d (a : Fˣ) x => GlobalCoreSource.rationalPeriod T f (a : F) (g d x))
    (fun d (a : Fˣ) x => GlobalCoreSource.rationalPeriod T f (a : F)
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x))
    (fun d x => GlobalCoreSource.nonzero_rationalPeriod_hasSum T f (g d x) (hs₀ d x))
    (fun d x => GlobalCoreSource.nonzero_rationalPeriod_hasSum T f
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d x)
      (hs₁ d x))
    ha ha_norm hb hb_norm hθ hc₀ hc₁ hc₀_zero hc₁_zero

end ThetaGlobal.GlobalProjectDescent
