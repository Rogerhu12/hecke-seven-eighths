import HeckeGeneral.Analysis.SIntegerOrbitUnfolding

/-!
# The inverse norm-one variable on the Fourier side of orbital Poisson

Haar inversion preserves the upstairs measure on the actual commutative
norm-one group. The whole subgroup series is reindexed by inversion as
well. Thus the chosen fundamental domain need not itself be invariant
under inversion, and no such property is assumed.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "G" => sLocalMultiplicativeGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Inversion in both the Haar variable and subgroup index gives the same
actual radial profile, with no domain-invariance hypothesis. -/
theorem setIntegral_tsum_sLocalTensorTestFunction_inv_eq_profile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (p : G) :
    (∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
      sLocalTensorTestFunction K S φ ψ
        (p * (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G)))
          ∂sUnitHaarMeasure K S) =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨sLocalProductNorm K S p, sLocalProductNorm_pos K S p⟩ := by
  let f : T → ℂ := fun x => sLocalTensorTestFunction K S φ ψ (p * ((x⁻¹ : T) : G))
  have hf : Integrable f (sUnitHaarMeasure K S) :=
    (integrable_sLocalTensorTestFunction_orbit K S Γ φ ψ hψ hψsupport p).comp_inv
  have hunfold := integral_sUnitHaar_eq_setIntegral_tsum_smul K S Γ hf
  have hseries (x : T) :
      (∑' g : (sLocalNormOneGamma K S Γ).op, f (g • x)) =
      ∑' u : Γ, sLocalTensorTestFunction K S φ ψ
        (p * (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G))) := by
    rw [tsum_sLocalGamma_action K S Γ]
    let g : Γ → ℂ := fun u => sLocalTensorTestFunction K S φ ψ
      (p * (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G)))
    have hterm (u : Γ) : f (sLocalNormOneDiagonal K S (u : S.unit K) * x) = g u⁻¹ := by
      change sLocalTensorTestFunction K S φ ψ
        (p * ((sLocalDiagonal K S (u : S.unit K) * (x : G))⁻¹)) =
        sLocalTensorTestFunction K S φ ψ
          (p * (sLocalDiagonal K S ((u⁻¹ : Γ) : S.unit K) * (x : G)⁻¹))
      rw [Subgroup.coe_inv, map_inv, mul_inv_rev]
      congr 1
      exact congrArg (fun z : G => p * z) (mul_comm _ _)
    simp_rw [hterm]
    exact (Equiv.inv Γ).tsum_eq g
  calc
    _ = ∫ x in sUnitFundamentalDomain K S Γ,
        ∑' g : (sLocalNormOneGamma K S Γ).op, f (g • x) ∂sUnitHaarMeasure K S := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (hseries x).symm)
    _ = ∫ x : T, f x ∂sUnitHaarMeasure K S := hunfold.symm
    _ = sUnitOrbitalIntegral K S (sLocalTensorTestFunction K S φ ψ) p :=
      integral_inv_eq_self (fun x : T => sLocalTensorTestFunction K S φ ψ (p * (x : G)))
        (sUnitHaarMeasure K S)
    _ = _ := sUnitOrbitalIntegral_eq_profile K S _ p

end HeckeGeneral.Analysis
