import HeckeGeneral.Analysis.SUnitInverseUnfolding
import HeckeGeneral.Analysis.SIntegerSchwartzPullback
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# All S-integer sectors with the inverse norm-one Haar variable

The whole nonzero S-integer family is absolutely integrable after inversion
of the norm-one variable, by the actual compact-image estimate. It can then
be enumerated by all its orbits and subgroup elements. Haar inversion and
inversion of the subgroup index unfold each sector to the same radial profile.
The chosen fundamental domain is never assumed to be invariant under inversion.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
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
local notation "N" => NonzeroRingElements (Set.integer S K)
local notation "Q" => SIntegerOrbits K S Γ

/-- A genuine nonzero S-integer sector, with its actual radial norm, on the
inverse Fourier-side Haar variable. -/
theorem setIntegral_tsum_sIntegerOrbit_inv_eq_profile
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (a : N) :
    (∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
      sLocalTensorTestFunction K S φ ψ
        ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S a) *
          (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G)))
          ∂sUnitHaarMeasure K S) =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerElementNorm K S a).val,
          mul_pos r.property (sIntegerElementNorm K S a).property⟩ := by
  rw [setIntegral_tsum_sLocalTensorTestFunction_inv_eq_profile K S Γ φ ψ hψ hψsupport]
  congr 1
  apply Subtype.ext
  exact (sLocalProductNorm_mul K S _ _).trans
    (by rw [sLocalProductNorm_section]; rfl)

/-- The actual full profile series has the inverse-variable integral as its
sum. Absolute Fubini precedes every regrouping; all subgroup sectors remain. -/
theorem hasSum_sIntegerOrbitalProfile_inverse
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    HasSum (fun q : Q =>
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ,
        ∑' a : N, sIntegerSchwartzTerm K S φ ψ r a (x⁻¹) ∂sUnitHaarMeasure K S) := by
  letI : Countable Γ := (sLocalGammaActionEquiv K S Γ).injective.countable
  let e := nonzeroSIntegerEquivOrbitProduct K S Γ
  let ν := (sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)
  let F : N → T → ℂ := fun a x => sIntegerSchwartzTerm K S φ ψ r a x⁻¹
  have hF : ∀ a : N, Integrable (F a) ν :=
    integrable_sIntegerSchwartzTerm_comp_on_domain K S Γ φ ψ hψ hψsupport r
      (fun x : T => x⁻¹) continuous_inv
  have hnorm : Summable (fun a : N => ∫ x : T, ‖F a x‖ ∂ν) :=
    summable_integral_norm_sIntegerSchwartzTerm_comp_on_domain K S Γ φ ψ hψ hψsupport r
      (fun x : T => x⁻¹) continuous_inv
  have hint : Summable (fun a : N => ∫ x : T, F a x ∂ν) :=
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
            (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G))) := by
      change sLocalTensorTestFunction K S φ ψ
        (sLocalNormSection K S r * ((x⁻¹ : T) : G) *
          sLocalNonzeroIntegerDiagonal K S
            ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm (q, u))) = _
      rw [sLocalNonzeroIntegerDiagonal_orbitProduct_symm]
      congr 1
      ac_rfl
    calc
      _ = ∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
          sLocalTensorTestFunction K S φ ψ
            ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S q.out) *
              (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G)))
            ∂sUnitHaarMeasure K S := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => tsum_congr (fun u => hterm u x))
      _ = _ := by
        rw [setIntegral_tsum_sIntegerOrbit_inv_eq_profile K S Γ φ ψ hψ hψsupport r q.out]
        rw [sIntegerOrbitNorm_out K S Γ q]
  have htotal : (∑' q : Q, ∑' u : Γ, ∫ x : T, F (e.symm (q, u)) x ∂ν) =
      ∫ x : T, ∑' a : N, F a x ∂ν := by
    rw [← hprod.tsum_prod]
    exact (e.symm.tsum_eq (fun a : N => ∫ x : T, F a x ∂ν)).trans
      (integral_tsum_of_summable_integral_norm hF hnorm)
  change HasSum _ (∫ x : T, ∑' a : N, F a x ∂ν)
  rw [← htotal]
  exact hprod.prod.hasSum.congr_fun (fun q => (hq q).symm)

end HeckeGeneral.Analysis
