import HeckeGeneral.Arithmetic.SIntegerMovingPeriodTraceTransport
/-! Exact scalar/compact-shape parametrization of the
actual moving period lattice. The ordinary correcting unit belongs to the
pullback of the original Gamma; all finite class sectors remain present. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain HeckeGeneral.Analysis
open NumberField.mixedEmbedding
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Multiplication by an actual ordinary unit preserves any integral ideal,
including every fixed class representative. -/
theorem ordinaryUnit_span_mul_integral (u : (𝓞 K)ˣ) (I : Ideal (𝓞 K)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (u : 𝓞 K)) *
      (I : FractionalIdeal (𝓞 K)⁰ K) = I := by
  calc
    _ = ((Ideal.span ({(u : 𝓞 K)} : Set (𝓞 K)) * I : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
    _ = _ := by rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.top_mul]

def tracePositiveScalarEquiv (ρ : ℝ) (hρ : 0 < ρ) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ] mixedEmbedding.euclidean.mixedSpace K where
  toLinearEquiv :=
    { toFun := fun v => ρ • v
      invFun := fun v => ρ⁻¹ • v
      left_inv := by intro v; simp [smul_smul, hρ.ne']
      right_inv := by intro v; simp [smul_smul, hρ.ne']
      map_add' := by intro v w; exact smul_add ρ v w
      map_smul' := by intro a v; exact smul_comm ρ a v }
  continuous_toFun := continuous_const_smul ρ
  continuous_invFun := continuous_const_smul ρ⁻¹

@[simp] theorem tracePositiveScalarEquiv_apply (ρ : ℝ) (hρ : 0 < ρ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    tracePositiveScalarEquiv K ρ hρ v = ρ • v := rfl

theorem movingPeriod_shape_nonzero
    {Δ : Subgroup (𝓞 K)ˣ} (z : FiniteIndexArchShape K Δ) :
    ∀ w, mixedEmbedding.normAtPlace w z.val ≠ 0 := by
  apply mixedEmbedding.norm_ne_zero_iff.mp
  rw [norm_eq_one_of_mem_finiteIndexBalancedShape K Δ z.property]
  exact one_ne_zero

/-- Scalar multiplication commutes with the actual trace coordinate change;
this is an equality of continuous linear equivalences, not only of sets. -/
theorem traceCoordinateMulEquiv_positive_scale
    (ρ : ℝ) (hρ : 0 < ρ) (z : mixedSpace K)
    (hz : ∀ w, mixedEmbedding.normAtPlace w z ≠ 0)
    (hρz : ∀ w, mixedEmbedding.normAtPlace w (ρ • z) ≠ 0) :
    traceCoordinateMulEquiv K (ρ • z) hρz =
      (traceCoordinateMulEquiv K z hz).trans (tracePositiveScalarEquiv K ρ hρ) := by
  ext v
  apply (traceToMixed K).injective
  simp only [ContinuousLinearEquiv.trans_apply, tracePositiveScalarEquiv_apply,
    map_smul, traceCoordinateMulEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, mixedCoordinateMulEquiv_apply]
  exact smul_mul_assoc ρ z (traceToMixed K v)

private theorem imageLattice_trans
    (L : Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K))
    (e f : mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K) :
    imageLattice L (e.trans f) = imageLattice (imageLattice L e) f := by
  ext v
  rfl

private theorem fieldScalar_nonzero (x : K) (hx : x ≠ 0) :
    ∀ w, mixedEmbedding.normAtPlace w (mixedEmbedding K x) ≠ 0 := by
  intro w
  rw [mixedEmbedding.normAtPlace_apply]
  exact (map_ne_zero w).mpr hx

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (M : (Ideal (𝓞 K))⁰)

/-- Uniform compact-shape inverse bound and exact scaled lattice identity
for every actual moving modulus. Gamma and the correcting unit are literal;
no torsion quotient or single ideal-class restriction is taken. -/
theorem exists_uniform_movingPeriod_scaled_shape
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
            (tracePositiveScalarEquiv K (arithmeticNormRoot K (mixedEmbedding K x)) hρ) := by
  obtain ⟨B, hB, hbound⟩ := exists_originalSubgroup_shape_inverse_bound K S Γ
  refine ⟨B, hB, fun c => ?_⟩
  obtain ⟨q, x, hx, hclass⟩ := exists_movingPeriod_class_scalar K S M c
  have hn : mixedEmbedding.norm (mixedEmbedding K x) ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr (fieldScalar_nonzero K x hx)
  let ρ := arithmeticNormRoot K (mixedEmbedding K x)
  have hρ : 0 < ρ := arithmeticNormRoot_pos K hn
  obtain ⟨u, hu⟩ := exists_subgroup_unit_normalize_mem K (ordinaryUnitPullback K S Γ) hn
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
        ((sIntegerMovingPeriod K S M c).val : FractionalIdeal (𝓞 K)⁰ K) := by
    calc
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K)) *
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
              ((periodClassRepresentative K q).val : FractionalIdeal (𝓞 K)⁰ K)) := by
        rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = _ := by
        rw [hclass]
        exact ordinaryUnit_span_mul_integral K (u : (𝓞 K)ˣ) _
  have hlat := traceIdealLattice_of_scalar_eq K _ _ ux hux0 hcorrected
  have hshape : ∀ w, mixedEmbedding.normAtPlace w (ρ • z.val) ≠ 0 := by
    rw [← hux]
    exact fieldScalar_nonzero K ux hux0
  have heq : traceCoordinateMulEquiv K (mixedEmbedding K ux)
      (fieldScalar_nonzero K ux hux0) =
        (traceCoordinateMulEquiv K z (movingPeriod_shape_nonzero K z)).trans
          (tracePositiveScalarEquiv K ρ hρ) := by
    simpa only [hux] using
      traceCoordinateMulEquiv_positive_scale K ρ hρ z (movingPeriod_shape_nonzero K z) hshape
  refine ⟨q, x, hx, u, z, hρ, hclass, rfl, hbound z, ?_⟩
  rw [heq, imageLattice_trans] at hlat
  exact hlat

end HeckeGeneral.Arithmetic
