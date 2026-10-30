import HeckeGeneral.Arithmetic.SIntegerMovingPeriodCompactShape
import Mathlib.RingTheory.FractionalIdeal.Norm

/-! Arithmetic scale of the actual moving period,
derived from the literal scalar ideal equality and the fractional-ideal
norm homomorphism. No determinant or lattice-norm covariance is assumed.
The final theorem uses the class-scalar equality exported by the compact-shape
proof to obtain the norm identity for exactly the same witnesses. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain HeckeGeneral.Analysis
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (M : (Ideal (𝓞 K))⁰)

/-- The degree-th power of the actual scalar length is the exact ratio of
ordinary ideal norms, including the fixed exceptional-prime product. -/
theorem movingPeriod_scalar_norm_scale
    (c : NonzeroRingElements (S.integer K))
    (q : ClassGroup (𝓞 K)) (x : K)
    (hclass : FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
          ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K)) :
    arithmeticNormRoot K (mixedEmbedding K x) ^ Module.finrank ℚ K =
      (Ideal.absNorm (sIntegerMovingPeriod K S M c).val : ℝ) /
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

/-- Actual witnesses, rather than a proposed norm-covariance assumption:
every moving period has a finite-sector scalar and its proved scale ratio. -/
theorem exists_movingPeriod_class_scalar_with_norm_scale
    (c : NonzeroRingElements (S.integer K)) :
    ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
        ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K) ∧
      arithmeticNormRoot K (mixedEmbedding K x) ^ Module.finrank ℚ K =
        (Ideal.absNorm (sIntegerMovingPeriod K S M c).val : ℝ) /
          (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) := by
  obtain ⟨q, x, hx, hclass⟩ := exists_movingPeriod_class_scalar K S M c
  exact ⟨q, x, hx, hclass, movingPeriod_scalar_norm_scale K S M c q x hclass⟩

/-- One simultaneous witness family: the bound is chosen before the moving
modulus, and its actual class/scalar, subgroup correction, compact shape,
scaled lattice identity and arithmetic norm ratio use the same witnesses. -/
theorem exists_uniform_movingPeriod_scaled_shape_with_norm_scale
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ B : ℝ, 0 < B ∧ ∀ c : NonzeroRingElements (S.integer K),
      ∃ q : ClassGroup (𝓞 K), ∃ x : K, ∃ hx : x ≠ 0,
      ∃ u : ordinaryUnitPullback K S Γ,
      ∃ z : FiniteIndexArchShape K (ordinaryUnitPullback K S Γ),
      ∃ hρ : 0 < arithmeticNormRoot K (mixedEmbedding K x),
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K) =
            ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K) ∧
        z.val = (arithmeticNormRoot K (mixedEmbedding K x))⁻¹ •
          ((u : (𝓞 K)ˣ) • mixedEmbedding K x) ∧
        ‖(traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)).symm.toContinuousLinearMap‖ ≤ B ∧
        traceIdealLattice K (integralIdealUnit K (sIntegerMovingPeriod K S M c)) =
          imageLattice
            (imageLattice
              (traceIdealLattice K (integralIdealUnit K (periodClassRepresentative K q)))
              (traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)))
            (tracePositiveScalarEquiv K (arithmeticNormRoot K (mixedEmbedding K x)) hρ) ∧
        arithmeticNormRoot K (mixedEmbedding K x) ^ Module.finrank ℚ K =
          (Ideal.absNorm (sIntegerMovingPeriod K S M c).val : ℝ) /
            (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) := by
  obtain ⟨B, hB, hshape⟩ := exists_uniform_movingPeriod_scaled_shape K S M Γ
  refine ⟨B, hB, fun c => ?_⟩
  obtain ⟨q, x, hx, u, z, hρ, hclass, hz, hbound, hlat⟩ := hshape c
  exact ⟨q, x, hx, u, z, hρ, hclass, hz, hbound, hlat,
    movingPeriod_scalar_norm_scale K S M c q x hclass⟩

end HeckeGeneral.Arithmetic
