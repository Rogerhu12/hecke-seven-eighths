import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalAnnularBounds
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SchwartzEulerControl

/-!
# Actual original ideal volume on the fixed positive annulus

The MOM_PRIME contour theorem supplies the genuine principal residue
and the uniform error for every positive scale.  Its Euler seminorm is
bounded here by a continuous finite Schwartz seminorm, chosen before
the test and scale.  Thus the original analytic input is proved, with
the support premise needed by the actual source retained explicitly.

This does not claim a volume theorem for arbitrary Schwartz functions
without that support premise.  In particular it does not construct the
stronger unrestricted VolumePrimitive by forgetting the annulus.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMoment
open MOM_PRIME
open scoped Classical BigOperators SchwartzMap NNReal

variable {K : Type} [Field K] [NumberField K]

/-- The actual principal residue times the original profile integral. -/
def actualAnnularDensity (chi : HeckeCharacter K) (phi : 𝓢(ℝ, ℂ)) : ℂ :=
  heckeExceptionalPoleCoefficient K chi * exceptionalProfileIntegral (phi : ℝ → ℂ) 0

/-- The same continuation gives a continuous Schwartz error seminorm
on the fixed original annulus, uniformly over all positive scales. -/
theorem exists_actualAnnularVolumeSeminorm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (chi : HeckeCharacter K) (hchi : ExceptionalNormReduced K chi)
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ remainder : Seminorm ℂ (𝓢(ℝ, ℂ)), Continuous remainder ∧
      ∀ (phi : 𝓢(ℝ, ℂ)), tsupport phi ⊆ Icc lower upper →
      ∀ X : ℝ, 0 < X →
        ‖(∑' I : Ideal (𝓞 K), heckeExceptionalCharacter K chi I *
            phi ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * actualAnnularDensity chi phi‖ ≤
          remainder phi := by
  obtain ⟨n, C, hC, hvolume⟩ := exists_actualUnmaskedExceptional_bound K hcomplex chi hchi
  obtain ⟨orders, D, hD, hSchwartz⟩ :=
    exists_schwartz_annular_testSeminorm_bound lower upper hlower (n + 2) 0
  let factor : ℝ≥0 := ⟨2 * C * D, by positivity⟩
  let p : Seminorm ℂ (𝓢(ℝ, ℂ)) := orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
  let remainder : Seminorm ℂ (𝓢(ℝ, ℂ)) := factor • p
  have hp : Continuous p := Seminorm.continuous_finsetSup
    (fun j _ => (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm j)
  have hr : Continuous remainder := by
    change Continuous (fun phi : 𝓢(ℝ, ℂ) => (factor : ℝ) * p phi)
    exact continuous_const.mul hp
  refine ⟨remainder, hr, ?_⟩
  intro phi hsupport X hX
  have hs : Function.support (phi : ℝ → ℂ) ⊆ Icc lower upper :=
    (subset_tsupport phi).trans hsupport
  let test : SmoothAnnularTest := {
    toFun := phi
    smooth := phi.smooth ⊤
    lower := lower
    upper := upper
    lower_pos := hlower
    upper_ge := hinterval
    support := hs }
  have h := hvolume test 0 X hX
  simp only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one,
    abs_zero, add_zero, one_pow] at h
  have hmain : volumeTerm (heckeExceptionalPoleCoefficient K chi)
      (exceptionalProfileIntegral test.toFun 0) 0 X =
        (X : ℂ) * actualAnnularDensity chi phi := by
    simp only [volumeTerm, Complex.ofReal_zero, mul_zero, add_zero, Complex.cpow_one]
    change heckeExceptionalPoleCoefficient K chi * (X : ℂ) *
      exceptionalProfileIntegral (phi : ℝ → ℂ) 0 = _
    unfold actualAnnularDensity
    ring
  rw [hmain] at h
  have hEuler : annularErrorSeminorm test n ≤ 2 * (D * p phi) :=
    (annularErrorSeminorm_le_testSeminorm test n (n + 2) le_rfl).trans
      (mul_le_mul_of_nonneg_left (hSchwartz phi hs) (by norm_num))
  calc
    _ ≤ C * annularErrorSeminorm test n := by
      simpa only [test] using h
    _ ≤ C * (2 * (D * p phi)) := mul_le_mul_of_nonneg_left hEuler hC.le
    _ = remainder phi := by
      change C * (2 * (D * p phi)) = (2 * C * D) * p phi
      ring


end HeckeSkeleton.Moments.EngineInduction
