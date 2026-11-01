import HeckeGeneral.Analysis.SUnitJointRadialProfile
import HeckeSkeleton.Moments.MOM_INV_STEP.FourierSeparation

/-!
# Actual Fourier separation of the common radial orbital kernel

A fixed smooth compact cutoff in the two logarithmic column norms turns
the genuine Haar orbital profile into a Schwartz function.  Fourier
inversion then separates the two columns with norm-one multipliers.
Smoothness comes from the proved Euler differentiation of the orbital
integral; neither a separation identity nor integrability of its Fourier
coefficients is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Bridge MeasureTheory
open scoped Classical ContDiff BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
variable (χ : LogPlane → ℂ) (hχ : ContDiff ℝ ∞ χ)
  (hχsupport : HasCompactSupport χ)

/-- The fixed cutoff times the genuine radial orbital profile, made into
a Schwartz function using the proved smoothness of that Haar integral. -/
def orbitalKernel (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap LogPlane ℂ :=
  (hχsupport.mul_right (f' := fun p =>
    sUnitJointRadialProfile K S φ ψ R 0 (logCoordinates p))).toSchwartzMap
      (hχ.mul ((contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0).comp
        logCoordinates.contDiff))

@[simp] theorem orbitalKernel_apply (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (p : LogPlane) :
    orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R p =
      χ p * sUnitJointRadialProfile K S φ ψ R 0 (logCoordinates p) := rfl

/-- The common Fourier density is constructed, and is integrable. -/
def orbitalDensity (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap LogPlane ℂ :=
  𝓕 (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R)

theorem orbitalDensity_integrable (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) :
    Integrable (orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) :=
  (orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R).integrable
    (μ := (volume : Measure LogPlane))

/-- The exact dual radial packet at two positive column norms.  The
cutoff-one condition concerns the fixed admissible column range only. -/
theorem orbitalProfile_separated (φ : SchwartzMap V ℂ)
    (R x y : {r : ℝ // 0 < r})
    (hcut : χ (logPoint (Real.log x.val) (Real.log y.val)) = 1) :
    sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
      ⟨R.val / (x.val * y.val), div_pos R.property (mul_pos x.property y.property)⟩ =
    ∫ ξ : LogPlane, orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ *
      columnPhase ξ.fst (Real.log x.val) * columnPhase ξ.snd (Real.log y.val) := by
  have he := schwartz_separated
    (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R)
    (logPoint (Real.log x.val) (Real.log y.val))
  rw [orbitalKernel_apply, hcut, one_mul] at he
  have hp := sUnitJointRadialProfile_at_logs K S φ ψ R x y 0
  rw [traceSchwartzEulerIterCLM_zero] at hp
  exact hp.symm.trans he

/-- The literal finite two-column orbital source is separated using
one common actual Fourier density before either Cauchy--Schwarz step. -/
theorem finite_orbitalProfile_separated {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (x : ι → {r : ℝ // 0 < r}) (y : κ → {r : ℝ // 0 < r})
    (a : ι → ℂ) (b : κ → ℂ)
    (hcut : ∀ i ∈ T, ∀ j ∈ U,
      χ (logPoint (Real.log (x i).val) (Real.log (y j).val)) = 1) :
    (∑ i ∈ T, ∑ j ∈ U, a i * b j *
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((x i).val * (y j).val),
          div_pos R.property (mul_pos (x i).property (y j).property)⟩) =
    ∫ ξ : LogPlane, orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ *
      (∑ i ∈ T, a i * columnPhase ξ.fst (Real.log (x i).val)) *
      (∑ j ∈ U, b j * columnPhase ξ.snd (Real.log (y j).val)) := by
  calc
    _ = ∑ i ∈ T, ∑ j ∈ U, a i * b j *
        orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R
          (logPoint (Real.log (x i).val) (Real.log (y j).val)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [orbitalKernel_apply, hcut i hi j hj, one_mul]
      have hp := sUnitJointRadialProfile_at_logs K S φ ψ R (x i) (y j) 0
      rw [traceSchwartzEulerIterCLM_zero] at hp
      exact congrArg (fun z : ℂ => a i * b j * z) hp.symm
    _ = _ := finite_bilinear_separated T U
      (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R)
      (fun i => Real.log (x i).val) (fun j => Real.log (y j).val) a b

/-- The separated finite source is an honest integrable expression. -/
theorem integrable_finite_orbitalProfile {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (x : ι → {r : ℝ // 0 < r}) (y : κ → {r : ℝ // 0 < r})
    (a : ι → ℂ) (b : κ → ℂ) :
    Integrable (fun ξ : LogPlane =>
      orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ *
        (∑ i ∈ T, a i * columnPhase ξ.fst (Real.log (x i).val)) *
        (∑ j ∈ U, b j * columnPhase ξ.snd (Real.log (y j).val))) :=
  integrable_finite_bilinear T U
    (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R)
    (fun i => Real.log (x i).val) (fun j => Real.log (y j).val) a b

end HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
