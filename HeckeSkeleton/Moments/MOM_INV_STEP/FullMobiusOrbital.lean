module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FullMobius
public import HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

/-!
# The genuine coprime orbital source produces two positive columns

This applies the full mutual-gcd extension to the actual Haar orbital
profile at radius R/(xy). The cutoff is one on the supported normalized
columns. The left side therefore contains the original full kernel;
the right side uses its actual common Fourier density. In particular,
neither a separated-source identity nor an energy bound is assumed.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.FullMobius

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Bridge MeasureTheory
open HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
open scoped Classical BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem genuine_orbital_source_energy
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : LogPlane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχsupport : HasCompactSupport χ)
    {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (A : ι → Ideal (𝓞 K)) (B : κ → Ideal (𝓞 K))
    (hA : ∀ i ∈ T, A i ≠ ⊥) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (x : ι → {r : ℝ // 0 < r}) (y : κ → {r : ℝ // 0 < r})
    (a : ι → ℂ) (b : κ → ℂ)
    (hcut : ∀ i ∈ T, ∀ j ∈ U,
      χ (logPoint (Real.log (x i).val) (Real.log (y j).val)) = 1) :
    ‖∑ i ∈ T, ∑ j ∈ U, if IsCoprime (A i) (B j) then
      a i * b j * sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((x i).val * (y j).val),
          div_pos R.property (mul_pos (x i).property (y j).property)⟩ else 0‖ ≤
      Real.sqrt (∑ D ∈ divisorPool T A, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
        ∫ ξ : LogPlane, ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ *
          ‖∑ i ∈ T with D ∣ A i, a i * columnPhase ξ.fst (Real.log (x i).val)‖ ^ 2) *
      Real.sqrt (∑ D ∈ divisorPool T A, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
        ∫ ξ : LogPlane, ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ *
          ‖∑ j ∈ U with D ∣ B j, b j * columnPhase ξ.snd (Real.log (y j).val)‖ ^ 2) := by
  let F := orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R
  have hprofile (i : ι) (hi : i ∈ T) (j : κ) (hj : j ∈ U) :
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((x i).val * (y j).val),
          div_pos R.property (mul_pos (x i).property (y j).property)⟩ =
        F (logPoint (Real.log (x i).val) (Real.log (y j).val)) := by
    rw [show F = orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R from rfl,
      orbitalKernel_apply, hcut i hi j hj, one_mul]
    have hp := sUnitJointRadialProfile_at_logs K S φ ψ R (x i) (y j) 0
    rw [traceSchwartzEulerIterCLM_zero] at hp
    exact hp.symm
  have he : (∑ i ∈ T, ∑ j ∈ U, if IsCoprime (A i) (B j) then
      a i * b j * sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((x i).val * (y j).val),
          div_pos R.property (mul_pos (x i).property (y j).property)⟩ else 0) =
      ∑ i ∈ T, ∑ j ∈ U, if IsCoprime (A i) (B j) then
        a i * b j * F (logPoint (Real.log (x i).val) (Real.log (y j).val)) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hprofile i hi j hj]
  rw [he]
  exact full_mobius_energy T U A B hA F
    (fun i => Real.log (x i).val) (fun j => Real.log (y j).val) a b

end HeckeSkeleton.Moments.MOMInvStep.FullMobius

end
