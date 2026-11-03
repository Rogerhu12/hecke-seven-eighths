import HeckeGeneral.Analysis.SIntegerMovingPeriodPolarTail
import Mathlib.Tactic

/-!
Uniform forward shape for every actual nonzero integral ideal.

UNCOMPILED independent candidate. This extends the existing moving-period
class-scalar and compact-shape argument to an arbitrary ideal I. The correcting
ordinary unit belongs to the pullback of the given finite-index S-unit subgroup.
No proposed lattice shape, scale identity, or operator bound is a premise.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ActualIdealTraceUniformShapeDraft

open NumberField IsDedekindDomain HeckeGeneral.Analysis HeckeGeneral.Arithmetic
open NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Actual finite class reduction, without a restriction to principal ideals. -/
theorem exists_ideal_class_scalar (I : (Ideal (𝓞 K))⁰) :
    ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
        (I.val : FractionalIdeal (𝓞 K)⁰ K) := by
  let q := ClassGroup.mk0 I
  obtain ⟨x, hx, heq⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mp
      (periodClassRepresentative_class K q)
  exact ⟨q, x, hx, heq⟩

/-- The scalar length is derived from the fractional-ideal norm homomorphism. -/
theorem ideal_scalar_norm_scale (I : (Ideal (𝓞 K))⁰)
    (q : ClassGroup (𝓞 K)) (x : K)
    (hclass : FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
          (I.val : FractionalIdeal (𝓞 K)⁰ K)) :
    arithmeticNormRoot K (mixedEmbedding K x) ^ Module.finrank ℚ K =
      (Ideal.absNorm I.val : ℝ) /
        (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) := by
  have hq := congrArg (FractionalIdeal.absNorm (R := 𝓞 K) (K := K)) hclass
  rw [map_mul, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm] at hq
  have hr := congrArg (fun r : ℚ => (r : ℝ)) hq
  push_cast at hr
  have hden : (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors (periodClassRepresentative K q)
  rw [arithmeticNormRoot_pow, mixedEmbedding.norm_eq_norm]
  apply (eq_div_iff hden).mpr
  simpa only [Rat.cast_abs] using hr

private theorem fieldScalar_nonzero (x : K) (hx : x ≠ 0) :
    ∀ w, mixedEmbedding.normAtPlace w (mixedEmbedding K x) ≠ 0 := by
  intro w
  rw [mixedEmbedding.normAtPlace_apply]
  exact (map_ne_zero w).mpr hx

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- One forward-shape constant works for every nonzero integral ideal.
The image equivalence and the positive scalar use the same class and balanced
generator. The finite-index subgroup is the original subgroup, not a newly
chosen larger unit group. -/
theorem exists_uniform_ideal_trace_shape
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ C : ℝ, 0 < C ∧ ∀ I : (Ideal (𝓞 K))⁰,
      ∃ q : ClassGroup (𝓞 K), ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ∃ e : V ≃L[ℝ] V,
        traceIdealLattice K (integralIdealUnit K I) =
          imageLattice (traceIdealLattice K
            (integralIdealUnit K (periodClassRepresentative K q))) e ∧
        ρ ^ Module.finrank ℚ K =
          (Ideal.absNorm I.val : ℝ) /
            (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) ∧
        ‖e.toContinuousLinearMap‖ ≤ ρ * C := by
  obtain ⟨C, hC, hforward⟩ := exists_movingPeriod_shape_forward_bound K S Γ
  refine ⟨C, hC, fun I => ?_⟩
  obtain ⟨q, x, hx, hclass⟩ := exists_ideal_class_scalar K I
  have hn : mixedEmbedding.norm (mixedEmbedding K x) ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr (fieldScalar_nonzero K x hx)
  let ρ := arithmeticNormRoot K (mixedEmbedding K x)
  have hρ : 0 < ρ := arithmeticNormRoot_pos K hn
  obtain ⟨u, hu⟩ :=
    exists_subgroup_unit_normalize_mem K (ordinaryUnitPullback K S Γ) hn
  let z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ) := ⟨_, hu⟩
  let ux : K := algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K) * x
  have hux0 : ux ≠ 0 := mul_ne_zero
    (((u : (𝓞 K)ˣ).isUnit.map (algebraMap (𝓞 K) K)).ne_zero) hx
  have hux : mixedEmbedding K ux = ρ • z.val := by
    change mixedEmbedding K (algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K) * x) =
      ρ • (ρ⁻¹ • ((u : (𝓞 K)ˣ) • mixedEmbedding K x))
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
    change mixedEmbedding K (algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K) * x) =
      mixedEmbedding K (algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K)) * mixedEmbedding K x
    exact map_mul (mixedEmbedding K) _ _
  have hcorrected : FractionalIdeal.spanSingleton (𝓞 K)⁰ ux *
      ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
        (I.val : FractionalIdeal (𝓞 K)⁰ K) := by
    calc
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K)) *
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
              ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K)) := by
        rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = _ := by
        rw [hclass]
        exact ordinaryUnit_span_mul_integral K (u : (𝓞 K)ˣ) I.val
  let e : V ≃L[ℝ] V :=
    (traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)).trans
      (tracePositiveScalarEquiv K ρ hρ)
  have hshape : ∀ w, mixedEmbedding.normAtPlace w (ρ • z.val) ≠ 0 := by
    rw [← hux]
    exact fieldScalar_nonzero K ux hux0
  have heq : traceCoordinateMulEquiv K (mixedEmbedding K ux)
      (fieldScalar_nonzero K ux hux0) = e := by
    simpa only [hux] using
      traceCoordinateMulEquiv_positive_scale K ρ hρ z (movingPeriod_shape_nonzero K z) hshape
  have hlat := traceIdealLattice_of_scalar_eq K (periodClassRepresentative K q) I ux hux0 hcorrected
  have hnorm := ideal_scalar_norm_scale K I q x hclass
  refine ⟨q, ρ, hρ, e, ?_, hnorm, ?_⟩
  · rw [heq] at hlat
    exact hlat
  · exact movingPeriod_scaled_forward_bound K
      (traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z))
      ρ C hρ hC.le (hforward z)

end HeckeGeneral.Arithmetic.ActualIdealTraceUniformShapeDraft
