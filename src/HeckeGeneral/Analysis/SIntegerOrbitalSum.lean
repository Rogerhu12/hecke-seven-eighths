import HeckeGeneral.Analysis.SIntegerSchwartzSummability
import HeckeGeneral.Analysis.SIntegerOrbitUnfolding
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Unfold all nonzero S-integers into the actual orbital profile

The uniform Schwartz bound supplies absolute summability of the integrals
over the actual fundamental domain. Only then is the nonzero S-integer sum
reindexed by its full orbit and subgroup element. Each inner subgroup sum
unfolds by Haar translation to the same genuine radial profile.

No convergence or integrability assumption is imposed on the test function
beyond its Schwartz property and the continuous, compactly supported finite
factor. The orbit index retains every sector and the radius is positive.
The separate additive zero term is not represented by a value of this profile.
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
local notation "I" => NonzeroRingElements (S.integer K)
local notation "Q" => SIntegerOrbits K S Γ

/-- All nonzero sectors are actually summable, and their sum is the integral
of the actual S-integer series on the chosen fundamental domain. -/
theorem hasSum_sIntegerOrbitalProfile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    HasSum (fun q : Q =>
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ,
        ∑' a : I, sIntegerSchwartzTerm K S φ ψ r a x ∂sUnitHaarMeasure K S) := by
  letI : Countable Γ := (sLocalGammaActionEquiv K S Γ).injective.countable
  let e := nonzeroSIntegerEquivOrbitProduct K S Γ
  let ν := (sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)
  let F : I → T → ℂ := sIntegerSchwartzTerm K S φ ψ r
  have hF : ∀ a : I, Integrable (F a) ν :=
    integrable_sIntegerSchwartzTerm_on_domain K S Γ φ ψ hψ hψsupport r
  have hnorm : Summable (fun a : I => ∫ x : T, ‖F a x‖ ∂ν) :=
    summable_integral_norm_sIntegerSchwartzTerm_on_domain K S Γ φ ψ hψ hψsupport r
  have hint : Summable (fun a : I => ∫ x : T, F a x ∂ν) :=
    hnorm.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  have hprod : Summable (fun p : Q × Γ => ∫ x : T, F (e.symm p) x ∂ν) :=
    e.symm.summable_iff.mpr hint
  have hq (q : Q) :
      (∑' u : Γ, ∫ x : T, F (e.symm (q, u)) x ∂ν) =
        sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
          ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
            mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩ := by
    have hj : Function.Injective (fun u : Γ => e.symm (q, u)) := by
      intro u v huv
      exact congrArg Prod.snd (e.symm.injective huv)
    have huNorm : Summable (fun u : Γ => ∫ x : T, ‖F (e.symm (q, u)) x‖ ∂ν) :=
      hnorm.comp_injective hj
    rw [integral_tsum_of_summable_integral_norm (fun u => hF (e.symm (q, u))) huNorm]
    have hterm (u : Γ) (x : T) : F (e.symm (q, u)) x =
        sLocalTensorTestFunction K S φ ψ
          ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S q.out) *
            (sLocalDiagonal K S (u : S.unit K) * (x : G))) := by
      change sLocalTensorTestFunction K S φ ψ
        (sLocalNormSection K S r * (x : G) *
          sLocalNonzeroIntegerDiagonal K S
            ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm (q, u))) = _
      rw [sLocalNonzeroIntegerDiagonal_orbitProduct_symm]
      congr 1
      ac_rfl
    calc
      _ = ∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
          sLocalTensorTestFunction K S φ ψ
            ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S q.out) *
              (sLocalDiagonal K S (u : S.unit K) * (x : G)))
            ∂sUnitHaarMeasure K S := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => tsum_congr (fun u => hterm u x))
      _ = _ := by
        rw [setIntegral_tsum_sIntegerOrbit_eq_profile K S Γ φ ψ hψ hψsupport r q.out]
        rw [sIntegerOrbitNorm_out K S Γ q]
  have htotal : (∑' q : Q, ∑' u : Γ, ∫ x : T, F (e.symm (q, u)) x ∂ν) =
      ∫ x : T, ∑' a : I, F a x ∂ν := by
    rw [← hprod.tsum_prod]
    exact (e.symm.tsum_eq (fun a : I => ∫ x : T, F a x ∂ν)).trans
      (integral_tsum_of_summable_integral_norm hF hnorm)
  change HasSum _ (∫ x : T, ∑' a : I, F a x ∂ν)
  rw [← htotal]
  exact hprod.prod.hasSum.congr_fun (fun q => (hq q).symm)

/-- Complex summability here is absolute, including every actual unit sector. -/
theorem summable_norm_sIntegerOrbitalProfile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun q : Q =>
      ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩‖) :=
  (hasSum_sIntegerOrbitalProfile K S Γ φ ψ hψ hψsupport r).summable.norm

end HeckeGeneral.Analysis
